#!/usr/bin/env python3
"""Collect exact source/native evidence without compiling or accepting a theorem.

Run after the requested native checks finish. This writes only --output, retains
raw successful and failed receipts/logs, and exits nonzero if evidence is missing.
It never writes ACCEPTANCE.json, changes register status, or invokes Lean.
"""
from __future__ import annotations
import argparse
from collections import defaultdict
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
IMPORT = re.compile(r"^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)", re.M)
FORBIDDEN = re.compile(r"\b(?:sorry|admit|native_decide)\b|^\s*(?:private\s+|public\s+)?axiom\b", re.M)
PROFILE_KEYS = ("heap_cap_mib", "rss_cap_mib", "wall_seconds", "cpu_seconds",
                "minimum_free_mib", "threads", "single_thread", "core_only_profile",
                "upstream_cache_only", "calculator_objects_borrowed")


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def uncomments(text: str) -> str:
    out, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith('/-', i):
            depth += 1; out.append('  '); i += 2
        elif depth and text.startswith('-/', i):
            depth -= 1; out.append('  '); i += 2
        elif not depth and text.startswith('--', i):
            end = text.find('\n', i)
            if end < 0:
                break
            out.append('\n'); i = end + 1
        else:
            out.append(text[i] if not depth or text[i] == '\n' else ' '); i += 1
    return ''.join(out)


def declared_aliases(text: str) -> list[str]:
    """Read public theorem names in the simple namespace-based statement gates."""
    scopes, result = [], []
    for line in uncomments(text).splitlines():
        line = re.sub(r'@\[[^]]*\]\s*', '', line).strip()
        match = re.match(r'namespace\s+(\S+)', line)
        if match:
            scopes.append(('namespace', match.group(1))); continue
        if re.match(r'(?:(?:public|private|meta)\s+)*section(?:\s|$)', line):
            scopes.append(('section', '')); continue
        if re.match(r'end(?:\s|$)', line):
            if scopes:
                scopes.pop()
            continue
        match = re.match(r'(?:(?:public|protected|noncomputable)\s+)*theorem\s+([^\s:(]+)', line)
        if match:
            name = match.group(1)
            prefix = '.'.join(name for kind, name in scopes if kind == 'namespace')
            result.append((prefix + '.' if prefix else '') + name)
    return result


def actual_axioms(log: str) -> tuple[dict[str, list[str]], list[str]]:
    pairs = re.findall(r'AXIOMS\s+([^\s:]+):\s*\[([^]]*)\]', log, re.S)
    pairs += re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", log, re.S)
    pairs += [(name, '') for name in re.findall(r"'([^']+)' does not depend on any axioms", log)]
    result, errors = {}, []
    for name, body in pairs:
        axioms = sorted(set(re.findall(r'[^\s,]+', body)))
        if name in result and result[name] != axioms:
            errors.append('Conflicting actual axiom lists for ' + name)
        result[name] = axioms
        if bad := sorted(set(axioms) - ALLOWED_AXIOMS):
            errors.append(name + ': forbidden axioms ' + ', '.join(bad))
    return result, errors


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, default=Path('/workspace/scratch/95d226e72a26/logic-lineages-papers'))
    parser.add_argument('--baseline', default='e5c70ae3')
    parser.add_argument('--root-module', action='append', required=True)
    parser.add_argument('--gate-module', action='append', default=[])
    parser.add_argument('--freeze', type=Path, action='append', default=[])
    parser.add_argument('--preserve-pins', type=Path, action='append', default=[])
    parser.add_argument('--allow-baseline-change', action='append', default=[], help='Exact repository path; always reported explicitly.')
    parser.add_argument('--receipt-dir', type=Path, action='append', default=[])
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    repo, output = args.repo.resolve(), args.output.resolve()
    root, calculator = repo/'formalization', repo/'04-pure-r1-calculator/lean'
    output.mkdir(parents=True, exist_ok=True)
    (output/'receipts').mkdir(exist_ok=True)
    errors, copied, sources, deps, external = [], {}, {}, {}, set()
    timestamp = datetime.now(timezone.utc).isoformat()

    def git(*argv: str) -> bytes:
        return subprocess.check_output(['git', *argv], cwd=repo)

    baseline = git('rev-parse', args.baseline + '^{commit}').decode().strip()

    def source_for(module: str) -> Path | None:
        base = calculator if module == 'R1Calculator' or module.startswith('R1Calculator.') else root
        path = base/(module.replace('.', '/') + '.lean')
        return path if path.is_file() else None

    visiting = set()
    order = []

    def visit(module: str) -> None:
        if module in sources:
            return
        if module in visiting:
            raise ValueError('Circular import: ' + module)
        path = source_for(module)
        if path is None:
            external.add(module); return
        visiting.add(module)
        data = path.read_bytes(); code = uncomments(data.decode())
        if FORBIDDEN.search(code):
            errors.append('Forbidden proof token in ' + module)
        own_deps = []
        for line in IMPORT.findall(code):
            for dep in line.split():
                if source_for(dep) is not None:
                    own_deps.append(dep)
                visit(dep)
        sources[module] = {'path': str(path.relative_to(repo)), 'sha256': sha(data)}
        deps[module] = own_deps
        visiting.remove(module); order.append(module)

    for module in dict.fromkeys(args.root_module + args.gate_module):
        if source_for(module) is None:
            errors.append('Requested local source absent: ' + module)
        else:
            visit(module)

    def resolve_file(name: str | Path) -> Path:
        name = Path(name)
        if name.is_absolute():
            return name
        candidates = [p for p in (repo/name, root/name) if p.exists()]
        if len(candidates) > 1 and candidates[0].resolve() != candidates[1].resolve():
            raise ValueError('Ambiguous file reference: ' + str(name))
        return candidates[0] if candidates else repo/name

    def verify_pins(path: Path) -> dict:
        path = resolve_file(path); raw = path.read_bytes(); doc = json.loads(raw)
        pins = {}
        def add(name, expected):
            if not isinstance(name, str) or not isinstance(expected, str) or not re.fullmatch('[0-9a-f]{64}', expected):
                return
            file = resolve_file(name)
            key = str(file.relative_to(repo)) if file.is_relative_to(repo) else str(file)
            if key in pins and pins[key] != expected:
                errors.append('Conflicting source pins: ' + key)
            pins[key] = expected
        def walk(item):
            if isinstance(item, list):
                for child in item:
                    walk(child)
            elif isinstance(item, dict):
                for path_key, hash_key in [('path','sha256'), ('source','source_sha256'), ('freeze_path','freeze_sha256')]:
                    if path_key in item and hash_key in item:
                        add(item[path_key], item[hash_key])
                for key, value in item.items():
                    if isinstance(value, str) and ('/' in key or key.endswith(('.lean','.json','.tex','.toml'))):
                        add(key, value)
                    elif isinstance(value, (dict, list)):
                        walk(value)
        walk(doc)
        if not pins:
            errors.append('No file pins found in ' + str(path))
        actual, mismatches = {}, []
        for name, expected in sorted(pins.items()):
            file = resolve_file(name)
            measured = sha(file.read_bytes()) if file.is_file() else None
            actual[name] = {'expected_sha256': expected, 'actual_sha256': measured, 'matches': expected == measured}
            if measured != expected:
                mismatches.append(name)
        if mismatches:
            errors.append('Frozen/preserved source mismatch in ' + str(path) + ': ' + ', '.join(mismatches))
        return {'path': str(path.relative_to(repo)) if path.is_relative_to(repo) else str(path),
                'sha256': sha(raw), 'file_count': len(pins), 'all_current_files_match': not mismatches,
                'mismatches': mismatches, 'files': actual}

    freezes = [verify_pins(p) for p in args.freeze]
    preserved = [verify_pins(p) for p in args.preserve_pins]

    baseline_names = set(git('ls-tree','-rz','--name-only',baseline).decode().split('\0')) - {''}
    changed_names = git('diff','--no-ext-diff','--name-only','-z',baseline,'--').decode().split('\0')
    baseline_changes = []
    allow = set(args.allow_baseline_change)
    for name in sorted(set(changed_names) & baseline_names):
        previous = git('show',baseline + ':' + name)
        current = repo/name
        baseline_changes.append({'path': name, 'baseline_sha256': sha(previous),
                                 'current_sha256': sha(current.read_bytes()) if current.is_file() else None,
                                 'explicitly_allowed': name in allow})
    unexpected = [x['path'] for x in baseline_changes if not x['explicitly_allowed']]
    if unexpected:
        errors.append('Unexpected baseline changes: ' + ', '.join(unexpected))
    baseline_report = {'schema': 'baseline-preservation-evidence-v1', 'baseline_commit': baseline,
                       'baseline_file_count': len(baseline_names), 'baseline_changes': baseline_changes,
                       'explicit_allowlist': sorted(allow), 'unexpected_changes': unexpected,
                       'all_baseline_files_unchanged': not baseline_changes,
                       'baseline_preserved_except_explicit_changes': not unexpected,
                       'all_baseline_lean_sources_unchanged': not any(x['path'].endswith('.lean') for x in baseline_changes),
                       'preserved_source_manifests': preserved}

    receipts, candidates, failed_rows, incomplete = [], defaultdict(list), [], []
    for directory in args.receipt_dir or [root/'build-reports']:
        directory = resolve_file(directory) if not directory.is_absolute() else directory
        for path in sorted(directory.glob('*.json')):
            if path.name == 'latest.json':
                continue
            try:
                data = path.read_bytes(); doc = json.loads(data)
            except (OSError, ValueError) as error:
                errors.append('Unreadable native receipt ' + str(path) + ': ' + str(error)); continue
            rows = doc.get('modules', [])
            if not any(row.get('module') in sources for row in rows) and not any(m in sources for m in doc.get('requested', [])):
                continue
            requested = doc.get('requested', [])
            successful = {row.get('module') for row in rows if row.get('returncode') == 0}
            complete = bool(requested) and all(m in successful for m in requested)
            whole_passed = complete and not doc.get('outcome') and all(row.get('returncode') == 0 for row in rows)
            terminated = any(row.get('returncode',0) != 0 for row in rows) or bool(doc.get('outcome'))
            if not complete and not terminated:
                incomplete.append(str(path)); continue
            dest = output/'receipts'/path.name
            dest.write_bytes(data); copied[str(dest.relative_to(output))] = sha(data)
            record = {'receipt': str(dest.relative_to(output)), 'sha256': sha(data),
                      'requested': requested, 'whole_receipt_passed': whole_passed,
                      'resource_profile': {key: doc.get(key) for key in PROFILE_KEYS}, 'module_rows': len(rows)}
            receipts.append(record)
            for row in rows:
                log_path = root/row['log'] if row.get('log') else None
                log_data = log_path.read_bytes() if log_path is not None and log_path.is_file() else None
                log_dest = output/'receipts'/log_path.name if log_path is not None else None
                if log_data is not None:
                    log_dest.write_bytes(log_data); copied[str(log_dest.relative_to(output))] = sha(log_data)
                details = {'receipt': record['receipt'], 'receipt_sha256': record['sha256'],
                           'whole_receipt_passed': whole_passed,
                           'log': str(log_dest.relative_to(output)) if log_dest else None,
                           'log_sha256': sha(log_data) if log_data is not None else None,
                           'resource_profile': record['resource_profile'], 'row': row}
                module = row.get('module')
                if row.get('returncode') not in (0, None):
                    failed_rows.append(details)
                if module in sources and row.get('returncode') == 0 and row.get('source_sha256') == sources[module]['sha256']:
                    if log_data is None:
                        errors.append('Successful source-matching row has no raw log: ' + module)
                    else:
                        candidates[module].append(details)

    matches, missing = {}, []
    for module in order:
        options = candidates[module]
        if not options:
            missing.append(module); continue
        selected = sorted(options, key=lambda v: (v['whole_receipt_passed'], v['receipt']))[-1]
        matches[module] = dict(sources[module], **selected)
    if missing:
        errors.append(str(len(missing)) + ' current local sources lack successful hash-matching native rows')

    root_results = {}
    for module in args.root_module:
        options = [v for v in candidates[module] if v['whole_receipt_passed']]
        root_results[module] = {'passed_in_complete_receipt': bool(options),
                                'receipt': options[-1]['receipt'] if options else None}
        if not options:
            errors.append('Focused root has no completed successful native receipt: ' + module)

    gates, all_gate_audits = {}, {}
    for module in args.gate_module:
        path = source_for(module)
        aliases = declared_aliases(path.read_text()) if path else []
        selected = matches.get(module)
        if not aliases:
            errors.append('No exact theorem aliases found in requested gate: ' + module)
        audits, audit_errors, passes = {}, [], []
        if selected:
            log = (output/selected['log']).read_text(errors='replace')
            audits, audit_errors = actual_axioms(log)
            passes = [{'namespace': ns, 'count': int(count)} for ns, count in
                      re.findall(r'AXIOM_AUDIT_PASS\s+([^\s:]+):\s*(\d+)\s+theorems', log)]
            for entry in passes:
                measured = sum(name.startswith(entry['namespace']+'.') for name in audits)
                if measured != entry['count']:
                    audit_errors.append('Logged audit namespace count does not match emitted declarations: ' + entry['namespace'])
            for ns in re.findall(r'#audit_namespace\s+(\S+)', uncomments(path.read_text())):
                if not any(p['namespace'] == ns for p in passes):
                    audit_errors.append('Missing native AXIOM_AUDIT_PASS for ' + ns)
        unaudited = [name for name in aliases if name not in audits]
        if unaudited:
            audit_errors.append('Missing actual alias axiom reports: ' + ', '.join(unaudited))
        errors.extend(audit_errors)
        gates[module] = {'exact_aliases': aliases, 'alias_count': len(aliases),
                         'actual_exact_alias_axioms': {name: audits[name] for name in aliases if name in audits},
                         'all_actual_logged_audits': audits, 'native_audit_passes': passes,
                         'audit_errors': audit_errors,
                         'native_evidence': selected}
        all_gate_audits.update({name: audits[name] for name in aliases if name in audits})

    artifact_checks = {}
    for module in order:
        artifact = root/'.lake/build/lib/lean'/(module.replace('.', '/') + '.olean')
        if not artifact.is_file() and module.startswith('R1Calculator'):
            artifact = calculator/'.lake/build/lib/lean'/(module.replace('.', '/') + '.olean')
        inputs = [repo/sources[module]['path']]
        for dep in deps[module]:
            dep_object = root/'.lake/build/lib/lean'/(dep.replace('.', '/') + '.olean')
            if not dep_object.is_file() and dep.startswith('R1Calculator'):
                dep_object = calculator/'.lake/build/lib/lean'/(dep.replace('.', '/') + '.olean')
            inputs.append(dep_object)
        fresh = artifact.is_file() and all(p.is_file() and artifact.stat().st_mtime_ns >= p.stat().st_mtime_ns for p in inputs)
        artifact_checks[module] = {'exists': artifact.is_file(), 'at_least_as_new_as_direct_inputs': fresh}
        if not fresh:
            errors.append('Local artifact absent/stale against direct inputs: ' + module)
    changed_during = [info['path'] for info in sources.values() if sha((repo/info['path']).read_bytes()) != info['sha256']]
    if changed_during:
        errors.append('Sources changed during evidence collection: ' + ', '.join(changed_during))

    native = {'schema': 'focused-native-evidence-v1', 'collected_at_utc': timestamp,
              'baseline_commit': baseline, 'root_modules': args.root_module,
              'gate_modules': args.gate_module, 'local_module_count': len(sources),
              'source_matched_local_module_count': len(matches), 'missing_source_matches': missing,
              'all_focused_sources_match_successful_native_rows': not missing,
              'successful_native_source_rows': matches, 'root_results': root_results,
              'gates': gates, 'exact_alias_count': sum(g['alias_count'] for g in gates.values()),
              'actual_exact_alias_axioms': all_gate_audits,
              'peak_successful_process_tree_rss_kib': max((v['row'].get('peak_process_tree_rss_kib',0) for v in matches.values()), default=0),
              'raw_receipts': receipts, 'failed_native_rows': failed_rows,
              'incomplete_receipts_excluded': incomplete, 'frozen_sources': freezes,
              'current_local_artifacts': artifact_checks, 'full_root_build': False,
              'remote_ci_claim': False, 'acceptance_decision': None,
              'evidence_complete': not errors, 'errors': errors}
    pins = {'schema': 'focused-source-pins-v1', 'collected_at_utc': timestamp,
            'baseline_commit': baseline, 'root_modules': args.root_module,
            'path_base': 'repository root', 'local_source_count': len(sources),
            'source_files': {v['path']: v['sha256'] for _,v in sorted(sources.items())},
            'local_imports': deps, 'direct_upstream_imports': sorted(external),
            'frozen_sources': freezes,
            'verifier_source_pins': {str(p.relative_to(repo)): sha(p.read_bytes()) for p in
                                    [root/'scripts/check.py', root/'LogicLineages/Audit.lean']}}
    for name, value in [('NATIVE-VERIFICATION.json',native), ('SOURCE-PINS.json',pins),
                        ('BASELINE-PRESERVATION.json',baseline_report)]:
        data = (json.dumps(value,indent=2)+'\n').encode(); (output/name).write_bytes(data); copied[name] = sha(data)
    manifest = {'schema': 'focused-evidence-artifacts-v1', 'files': dict(sorted(copied.items())),
                'collector_sha256': sha(Path(__file__).read_bytes()), 'excludes_self': True}
    (output/'EVIDENCE-MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
    print(json.dumps({'evidence_complete': not errors, 'local_modules': len(sources),
                      'source_matched_modules': len(matches), 'exact_alias_count': native['exact_alias_count'],
                      'error_count': len(errors), 'output': str(output)},indent=2))
    if errors:
        for error in errors[:15]:
            print('EVIDENCE_INCOMPLETE: ' + error)
    return 0 if not errors else 1


if __name__ == '__main__':
    sys.exit(main())
