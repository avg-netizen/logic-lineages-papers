#!/usr/bin/env python3
"""Prospective capture only. Refuses existing candidates or a failed/stale comparator.
Reconstructed 2026-11-02; does not claim recovery of the previous private helper.
Paths in the specification are repository-relative. Never invokes Lean.
"""
import argparse, datetime, hashlib, json, pathlib, re

def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def canonical(x):
    return (json.dumps(x, sort_keys=True, indent=2) + '\n').encode()

def within(root, value):
    p = (root / value).resolve()
    if not p.is_relative_to(root) or pathlib.Path(value).is_absolute():
        raise ValueError('Not repository-relative: ' + str(value))
    return p

def module_name(path):
    p = pathlib.PurePosixPath(path)
    assert p.parts[0] == 'formalization' and p.suffix == '.lean', path
    return '.'.join(p.with_suffix('').parts[1:])

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo', required=True, type=pathlib.Path)
    ap.add_argument('--spec', required=True, type=pathlib.Path)
    ap.add_argument('--receipt', required=True, type=pathlib.Path)
    ap.add_argument('--output', required=True, type=pathlib.Path)
    a = ap.parse_args(); root = a.repo.resolve()
    spec = json.loads(a.spec.read_text()); receipt = json.loads(a.receipt.read_text())
    assert not a.output.exists(), 'Freeze output already exists; no overwrite'
    assert spec['root_review_reference'].strip() and spec['scope'].strip()
    assert spec['source'] and spec['aliases'] and spec['candidate_files']
    assert receipt['modules'] and all(r['returncode'] == 0 for r in receipt['modules'])
    assert receipt.get('upstream_cache_only') is True and receipt.get('threads') == 1
    rows = {r['module']: r for r in receipt['modules']}
    frozen = []
    for entry in spec['frozen_files']:
        p = within(root, entry['path']); sha = digest(p)
        assert entry['role'] in {'definitions', 'target', 'gate', 'correspondence'}
        if entry['role'] in {'definitions', 'target'}:
            row = rows[module_name(entry['path'])]
            assert row['source_sha256'] == sha, 'Comparator source mismatch: ' + str(p)
        frozen.append(dict(entry, sha256=sha))
    assert any(e['role'] == 'target' for e in frozen)
    gates = [e for e in frozen if e['role'] == 'gate']; assert len(gates) == 1
    gate = within(root, gates[0]['path']).read_text()
    for alias in spec['aliases']:
        short = alias['declaration'].rsplit('.', 1)[-1]
        # Require literal frozen target annotation, not inferred alias types.
        pattern = r'\btheorem\s+' + re.escape(short) + r'\s*:\s*' + re.escape(alias['target']) + r'\s*:='
        assert re.search(pattern, gate), 'Missing exact annotated alias: ' + short
        assert '#audit_namespace ' + alias['namespace'] in gate, 'Missing namespace audit'
    candidates = []
    for entry in spec['candidate_files']:
        assert not within(root, entry['path']).exists(), 'Candidate already exists: ' + entry['path']
        candidates.append(dict(entry, exists=False))
    source = [dict(e, sha256=digest(within(root, e['path']))) for e in spec['source']]
    value = dict(spec, schema='author-freeze-v2', phase='before-candidate-authoring',
        observed_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
        spec_sha256=digest(a.spec), comparator_receipt_sha256=digest(a.receipt),
        comparator_receipt=str(a.receipt.resolve()), frozen_files=frozen,
        candidate_files=candidates, source=source,
        allowed_axioms=['propext', 'Classical.choice', 'Quot.sound'],
        capture_script_sha256=digest(pathlib.Path(__file__)))
    a.output.parent.mkdir(parents=True, exist_ok=True)
    with a.output.open('xb') as f: f.write(canonical(value))
    print(json.dumps({'path': str(a.output), 'sha256': digest(a.output), 'candidates_absent': len(candidates)}))

if __name__ == '__main__':
    main()
