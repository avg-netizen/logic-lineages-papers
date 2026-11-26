#!/usr/bin/env python3
"""Read-only native evidence verification. This never invokes Lean or changes sources.

Run from formalization, e.g.:
  python verification/continuation-2026-11-11/child-certificate/verify_evidence.py \
    --gate LogicLineages....StatementChecks --alias LogicLineages....exactAlias

Outputs a new dated evidence snapshot under this checkpoint. A successful
report verifies native receipts, not manuscript correspondence or adoption.
An active build can yield a pending snapshot; rerun after all jobs finish.
"""
from __future__ import annotations
import argparse
import os
import resource
from contextlib import contextmanager
from datetime import datetime, timezone
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = next(p for p in HERE.parents if (p / 'scripts/check.py').is_file())
REPO = ROOT.parent
spec = importlib.util.spec_from_file_location('original_checker', ROOT / 'scripts/check.py')
checker = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checker)
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
PROFILE = {'heap_cap_mib': 2048, 'rss_cap_mib': 1536, 'wall_seconds': 180,
           'cpu_seconds': 90, 'minimum_free_mib': 2048, 'core_only_profile': False,
           'single_thread': True, 'threads': 1, 'upstream_cache_only': True}


def sha(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b''): h.update(chunk)
    return h.hexdigest()


def git(*args):
    return subprocess.check_output(['git', '-C', str(REPO), *args], env={**os.environ, 'GIT_OPTIONAL_LOCKS':'0'}).decode()


def clean_source(text):
    # Identical comment-stripping logic to the unchanged native checker.
    code, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith('/-', i):
            depth += 1; code.append('  '); i += 2
        elif depth and text.startswith('-/', i):
            depth -= 1; code.append('  '); i += 2
        elif not depth and text.startswith('--', i):
            end = text.find('\n', i)
            if end < 0: break
            code.append('\n'); i = end + 1
        else:
            code.append(text[i] if not depth or text[i] == '\n' else ' '); i += 1
    return ''.join(code)


def closure(gates):
    order, visiting, visited, dependencies, external = [], set(), set(), {}, set()
    def visit(module):
        if module in visited: return
        if module in visiting: raise ValueError('Cyclic local import: ' + module)
        path = checker.source_for(module)
        if path is None: raise ValueError('Missing requested local module: ' + module)
        visiting.add(module)
        clean = clean_source(path.read_text())
        if re.search(r'\b(?:sorry|admit|native_decide)\b|^\s*(?:private\s+|public\s+)?axiom\b', clean, re.M):
            raise ValueError('Forbidden placeholder/axiom: ' + module)
        dependencies[module] = []
        for line in checker.IMPORT.findall(clean):
            for dep in line.split():
                if checker.source_for(dep) is not None:
                    dependencies[module].append(dep); visit(dep)
                else: external.add(dep)
        visiting.remove(module); visited.add(module); order.append(module)
    for gate in gates: visit(gate)
    return order, dependencies, sorted(external)


def frozen_records(frozen_path):
    rows = []
    for line in frozen_path.read_text().splitlines():
        expected, relative = line.split(maxsplit=1)
        relative = relative.lstrip('*')
        # Older coordinator entries may start with formalization/.
        path = REPO / relative if relative.startswith('formalization/') else ROOT / relative
        if not path.resolve().is_relative_to(ROOT):
            raise ValueError('Frozen path escapes formalization: ' + relative)
        actual = sha(path) if path.is_file() else None
        rows.append({'path':str(path.relative_to(ROOT)), 'expected':expected,
                     'actual':actual, 'matches':expected == actual})
    return rows


def inherited_records(base, allowed):
    names = set(git('ls-tree', '-r', '--name-only', base).splitlines())
    changed = set(git('diff', '--no-ext-diff', '--name-only', base, '--').splitlines())
    inherited_changes = sorted(names & changed)
    return {'baseline_commit':git('rev-parse',base).strip(),
            'baseline_tree':git('rev-parse',base+'^{tree}').strip(),
            'baseline_file_count':len(names), 'allowed_mutable_paths':sorted(allowed),
            'changed_inherited_paths':inherited_changes,
            'unexpected_changes':sorted(set(inherited_changes)-allowed)}


def parse_axioms(text):
    rows = {}
    for pattern in (r'^AXIOMS (\S+): \[([^\]]*)\]',
                    r"^'([^']+)' depends on axioms: \[([^\]]*)\]"):
        for name, body in re.findall(pattern, text, re.M):
            rows[name] = sorted(set(x.strip() for x in body.split(',') if x.strip()))
    for name in re.findall(r"^'([^']+)' does not depend on any axioms", text, re.M):
        rows[name] = []
    return rows


def write_json(path, value, compressed=False):
    if compressed:
        with gzip_text(path) as out:
            json.dump(value, out, indent=2, sort_keys=True); out.write('\n')
    else:
        with path.open('w') as out:
            json.dump(value, out, indent=2, sort_keys=True); out.write('\n')

@contextmanager
def gzip_text(path):
    import io
    with path.open('wb') as raw:
        with gzip.GzipFile(filename='', mode='wb', fileobj=raw, mtime=0, compresslevel=1) as z:
            with io.TextIOWrapper(z, encoding='utf-8') as text:
                yield text

def jsonline(out, value):
    # iterencode avoids a second full serialized copy of each receipt.
    json.dump(value, out, separators=(',', ':'), sort_keys=True)
    out.write('\n')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--frozen-file', type=Path, required=True)
    parser.add_argument('--gate', action='append', required=True)
    parser.add_argument('--alias', action='append', default=[])
    parser.add_argument('--base', default='6ff98ec9b0342adddb88c2375cf14a770fbae886')
    parser.add_argument('--allow-inherited', action='append', default=['formalization/AGENTS.md'])
    args = parser.parse_args()
    stamp = datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
    out = HERE / 'runs' / stamp
    out.mkdir(parents=True,exist_ok=False)
    errors, selected, log_paths, unreadable = [], {}, set(), []
    order, dependencies, external = closure(args.gate)
    digests = {m:sha(checker.source_for(m)) for m in order}
    receipt_count = failure_count = 0
    # EXACT old selection order: lexically sorted receipt path, then module row order.
    # Later failures never replace an earlier source-matched successful row.
    with gzip_text(out/'ATTEMPTS.jsonl.gz') as archive, gzip_text(out/'FAILED-RECEIPTS.jsonl.gz') as failed:
        for path in sorted((ROOT/'build-reports').glob('*.json')):
            if path.name == 'latest.json': continue
            try: receipt = json.loads(path.read_text())
            except (OSError,ValueError) as e:
                unreadable.append({'path':str(path.relative_to(ROOT)), 'error':str(e)}); continue
            key = str(path.relative_to(ROOT))
            jsonline(archive, {'path':key, 'receipt':receipt}); receipt_count += 1
            if receipt.get('outcome') or any(x.get('returncode',0) != 0 for x in receipt.get('modules',[])):
                jsonline(failed, {'path':key,'receipt':receipt}); failure_count += 1
            profile = {f:receipt.get(f) for f in PROFILE}
            for row in receipt.get('modules',[]):
                module = row['module']
                if module in digests and row.get('returncode') == 0 and row.get('source_sha256') == digests[module]:
                    selected[module] = (key, row, profile)
                log = row.get('log')
                if log and (ROOT/log).is_file(): log_paths.add(log)
        # Never retain all receipts, failed receipts, or their redundant module history.
    log_count = 0
    selected_logs = {row.get('log') for _, row, _ in selected.values()}
    archived_log_digests = {}
    with gzip_text(out/'NATIVE-LOGS.jsonl.gz') as archive:
        for log in sorted(log_paths):
            # Full normalized text, one readable JSONL record per log. Same read_text
            # semantics as legacy; peak memory is one log, not the whole history.
            text = (ROOT/log).read_text()
            jsonline(archive, {'path':log, 'text':text}); log_count += 1
            if log in selected_logs:
                archived_log_digests[log] = hashlib.sha256(text.encode()).hexdigest()
    rows, axioms, audits = [], {}, []
    for module in order:
        source = checker.source_for(module)
        digest = sha(source)
        if digest != digests[module]:
            errors.append('Source changed since receipt selection: '+module)
        if module not in selected:
            errors.append('No source-matched successful native row: '+module)
            rows.append({'module':module,'source_sha256':digest,'status':'pending'}); continue
        key, row, receipt = selected[module]
        for field,value in PROFILE.items():
            if receipt.get(field) != value:
                errors.append(f'Wrong native profile {field}: {key} ({module})')
        obj = checker.BUILD / (module.replace('.','/')+'.olean')
        artifacts = [obj,Path(str(obj)+'.private'),Path(str(obj)+'.server'),obj.with_suffix('.ir')]
        missing = [str(p.relative_to(ROOT)) for p in artifacts if not p.is_file()]
        if missing: errors.append('Missing native outputs: '+', '.join(missing))
        inputs = [source] + [checker.BUILD / (d.replace('.', '/')+'.olean')
                             for d in dependencies[module]]
        if obj.is_file() and any(not p.is_file() or p.stat().st_mtime_ns > obj.stat().st_mtime_ns
                                 for p in inputs):
            errors.append('Stale native output versus source/dependencies: '+module)
        log = row.get('log')
        if log not in log_paths: errors.append('Missing native log: '+module)
        text = (ROOT/log).read_text() if log in log_paths else ''
        if log in archived_log_digests and hashlib.sha256(text.encode()).hexdigest() != archived_log_digests[log]:
            errors.append('Selected native log changed since archival: '+module)
        parsed = parse_axioms(text); axioms.update(parsed)
        for name, ax in parsed.items():
            if set(ax)-ALLOWED: errors.append('Forbidden axioms: '+name+': '+str(ax))
        audits.extend({'namespace':name,'theorems':int(count),'module':module}
                      for name,count in re.findall(r'^AXIOM_AUDIT_PASS (\S+): (\d+) theorems',text,re.M))
        clean = clean_source(source.read_text())
        for namespace in re.findall(r'^#audit_namespace\s+(\S+)',clean,re.M):
            if not re.search(r'^AXIOM_AUDIT_PASS '+re.escape(namespace)+r': \d+ theorems',text,re.M):
                errors.append('Missing namespace axiom audit: '+namespace)
        rows.append({'module':module,'source':str(source.relative_to(REPO)),
                     'source_sha256':digest,'receipt':key,'native_row':row,
                     'objects':{str(p.relative_to(ROOT)):sha(p) for p in artifacts if p.is_file()},
                     'log_sha256':hashlib.sha256(text.encode()).hexdigest(),
                     'status':'native-source-matched'})
    errors.extend('Unreadable receipt during snapshot: '+r['path'] for r in unreadable)
    for r in rows:
        if sha(checker.source_for(r['module'])) != r['source_sha256']:
            errors.append('Source changed during snapshot: '+r['module'])
    for alias in args.alias:
        if alias not in axioms: errors.append('Missing exact alias axiom evidence: '+alias)
    frozen = frozen_records(args.frozen_file)
    errors.extend('Frozen specification mismatch: '+r['path'] for r in frozen if not r['matches'])
    inherited = inherited_records(args.base,set(args.allow_inherited))
    errors.extend('Changed inherited file: '+p for p in inherited['unexpected_changes'])
    write_json(out/'SOURCE-AND-OBJECTS.json.gz',rows,True)
    write_json(out/'FROZEN-PRESERVATION.json',frozen)
    write_json(out/'INHERITED-PRESERVATION.json',inherited)
    write_json(out/'AXIOMS.json',{'allowed':sorted(ALLOWED),'declarations':axioms,'namespace_audits':audits,
                                  'required_exact_aliases':args.alias})
    report = {'generated_at_utc':stamp,'status':'candidate-pending' if errors else 'candidate-checks-passed-not-adopted',
              'archive_schema':'bounded-jsonl-v1; receipt records path/receipt; log records path/text',
              'receipt_count':receipt_count,'failed_receipt_count':failure_count,'log_count':log_count,
              'peak_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
              'frozen_file':str(args.frozen_file),
              'candidate_review_required':True,
              'mathematical_acceptance':'requires coordinator source-correspondence and exact-gate review',
              'gate_roots':args.gate,'native_profile':PROFILE,'local_source_closure':len(order),
              'source_matched_native_modules':sum(r['status']=='native-source-matched' for r in rows),
              'direct_external_imports':external,'external_cache_claim':'not reverified by this script; use separate pinned restoration evidence',
              'checker_sha256':sha(ROOT/'scripts/check.py'),'verifier_sha256':sha(Path(__file__)),'errors':errors,'unreadable_receipts':unreadable,
              'full_root_build_claimed':False,'remote_ci_pass_claimed':False,
              'all_readable_failed_receipts_preserved':True,'all_receipts_readable':not unreadable,'snapshot_warning':'Concurrent sources/artifacts/receipts may change; source hashes rechecked. Unlike legacy receipt-loop rereads, logs are captured once in sorted path order after receipts, and selected logs reread during checks. Initial/current sources and selected archived/checked logs are compared; changes fail closed. Run quiescent for exact capture equivalence.'}
    write_json(out/'REPORT.json',report)
    print(json.dumps({'report':str((out/'REPORT.json').relative_to(ROOT)),'status':report['status'],
                      'modules':len(order),'errors':len(errors)},indent=2))
    return 1 if errors else 0

if __name__ == '__main__':
    sys.exit(main())
