"""Source-matched native evidence, streaming receipts rather than retaining all logs."""
import argparse
from datetime import datetime, timezone
import gzip
import importlib.util
import json
from pathlib import Path
import re

here = Path(__file__).resolve().parent
supplier = here.parent / 'continuation-2026-11-11/rank-guarded-representative-complete/verify_evidence.py'
spec = importlib.util.spec_from_file_location('inherited_evidence_verifier', supplier)
verifier = importlib.util.module_from_spec(spec)
spec.loader.exec_module(verifier)
verifier.HERE = here


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--gate', action='append', required=True)
    parser.add_argument('--alias', action='append', default=[])
    parser.add_argument('--base', default='9e732bf4a5f8a144d42b7359a19f38312cc78219')
    parser.add_argument('--allow-inherited', action='append', default=['formalization/AGENTS.md'])
    args = parser.parse_args()
    root = verifier.ROOT
    check = verifier.checker
    order, dependencies, external = verifier.closure(args.gate)
    digests = {m:check.file_digest(check.source_for(m)) for m in order}
    out = here / 'runs' / datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
    out.mkdir(parents=True)
    selected = {}
    # A receipt can repeat thousands of earlier rows. Keep only the latest
    # successful source-matched row, and read each selected log only once below.
    for path in sorted((root / 'build-reports').glob('*.json')):
        if path.name == 'latest.json':
            continue
        try:
            receipt = json.loads(path.read_text())
        except (OSError, ValueError):
            continue
        if any(receipt.get(k) != v for k,v in verifier.PROFILE.items()):
            continue
        for row in receipt.get('modules', []):
            module = row.get('module')
            if (module in digests and row.get('returncode') == 0 and
                    row.get('source_sha256') == digests[module]):
                selected[module] = (str(path.relative_to(root)), row)
    # Publish the selected receipt rows and original native logs without loading
    # every historical log/receipt into memory. Receipt subsets are explicitly
    # labelled; the unchanged full originals remain in local build-reports.
    groups = {}
    for module, (relative, row) in selected.items():
        groups.setdefault(relative, []).append(row)
    with gzip.open(out/'SELECTED-RECEIPT-ROWS.json.gz', 'wt') as stream:
        stream.write('{')
        for index, (relative, subset) in enumerate(groups.items()):
            receipt = json.loads((root/relative).read_text())
            value = {k:v for k,v in receipt.items() if k != 'modules'}
            value.update(modules=subset, selected_rows_only=True,
                         original_receipt_sha256=check.file_digest(root/relative))
            if index: stream.write(',')
            stream.write(json.dumps(relative)+':')
            json.dump(value, stream, sort_keys=True)
        stream.write('}')
    log_archive = gzip.open(out/'NATIVE-LOGS.json.gz', 'wt')
    log_archive.write('{')
    saved_logs = set()
    errors, rows, axioms, audits = [], [], {}, []
    for module in order:
        item = selected.get(module)
        if item is None:
            errors.append('Missing source-matched native row: ' + module)
            continue
        receipt, row = item
        target = check.BUILD / (module.replace('.', '/') + '.olean')
        objects = check.object_bundle(target)
        if any(value is None for value in objects.values()):
            errors.append('Missing native output bundle: ' + module)
        inputs = [check.source_for(module)] + [check.BUILD / (d.replace('.', '/')+'.olean')
                                             for d in dependencies[module]]
        if not target.is_file() or any(not p.is_file() or p.stat().st_mtime_ns > target.stat().st_mtime_ns
                                       for p in inputs):
            errors.append('Stale native object: ' + module)
        log = root / row['log']
        if not log.is_file():
            errors.append('Missing native log: ' + module)
            continue
        text = log.read_text()
        if row['log'] not in saved_logs:
            if saved_logs: log_archive.write(',')
            log_archive.write(json.dumps(row['log'])+':'+json.dumps(text))
            saved_logs.add(row['log'])
        parsed = verifier.parse_axioms(text)
        axioms.update(parsed)
        for name, foundations in parsed.items():
            if set(foundations) - verifier.ALLOWED:
                errors.append('Forbidden axioms: ' + name)
        source = check.source_for(module)
        clean = verifier.clean_source(source.read_text())
        for namespace in re.findall(r'^#audit_namespace\s+(\S+)', clean, re.M):
            match = re.search(r'^AXIOM_AUDIT_PASS '+re.escape(namespace)+r': (\d+) theorems', text, re.M)
            if match is None:
                errors.append('Missing namespace audit: ' + namespace)
            else:
                audits.append({'namespace':namespace,'theorems':int(match[1])})
        rows.append({'module':module,'source':str(source.relative_to(verifier.REPO)),
                     'source_sha256':digests[module], 'receipt':receipt, 'native_row':row,
                     'objects':{str(Path(p).relative_to(root)):value for p,value in objects.items()},
                     'log_sha256':check.file_digest(log)})
    log_archive.write('}')
    log_archive.close()
    for alias in args.alias:
        if alias not in axioms:
            errors.append('Missing exact alias axiom evidence: ' + alias)
    for module, expected in digests.items():
        if check.file_digest(check.source_for(module)) != expected:
            errors.append('Source changed during snapshot: ' + module)
    frozen = verifier.frozen_records()
    errors += ['Frozen source mismatch: '+r['path'] for r in frozen if not r['matches']]
    inherited = verifier.inherited_records(args.base, set(args.allow_inherited))
    errors += ['Changed inherited source: '+p for p in inherited['unexpected_changes']]
    report = {'passed':not errors, 'errors':errors, 'gates':args.gate,
              'exact_aliases':args.alias, 'module_count':len(order), 'native_rows':len(rows),
              'namespace_audits':audits, 'external_imports':external,
              'profile':verifier.PROFILE, 'full_root_build':False, 'remote_ci_claim':False,
              'native_logs':len(saved_logs), 'checker_sha256':check.file_digest(root/'scripts/check.py'),
              'verifier_sha256':check.file_digest(Path(__file__)),
              'external_cache_claim':'Pinned upstream artifacts reused; not recompiled by this check'}
    report['recovery_frozen_context'] = json.loads((here/'FROZEN-RECOVERY.json').read_text())
    for name, value in [('REPORT.json',report),('AXIOMS.json',axioms),
                        ('FROZEN-PRESERVATION.json',frozen),('INHERITED-PRESERVATION.json',inherited)]:
        (out/name).write_text(json.dumps(value,indent=2)+'\n')
    with gzip.open(out/'SOURCE-AND-OBJECTS.json.gz','wt') as stream:
        json.dump(rows,stream,sort_keys=True)
    print(json.dumps({'passed':not errors,'module_count':len(order), 'native_rows':len(rows),
                      'axiom_declarations':len(axioms),'errors':errors[:20], 'report':str(out/'REPORT.json')}))
    return int(bool(errors))


if __name__ == '__main__':
    raise SystemExit(main())
