#!/usr/bin/env python3
"""Verify archived checkpoint evidence against this checkout.

This is a read-only consistency check. It does not replace Lean, run a
compiler, accept a new theorem, or claim a fresh native build. Optional object
checking applies only when the matching local build artifacts are present.
"""
from __future__ import annotations
import argparse
from collections import Counter
import gzip
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
FORMAL = HERE.parents[2]
REPO = FORMAL.parent
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
PROFILE = {'heap_cap_mib': 2048, 'rss_cap_mib': 1536, 'minimum_free_mib': 2048,
           'wall_seconds': 180, 'cpu_seconds': 90, 'threads': 1,
           'single_thread': True, 'upstream_cache_only': True, 'core_only_profile': False}
IMPORT = re.compile(r'^\s*(?:(?:public|private|meta)\s+)*import\s+(.+)$', re.M)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def load(name):
    path = HERE / name
    raw = path.read_bytes()
    return json.loads(gzip.decompress(raw) if path.suffix == '.gz' else raw)

def source_for(module):
    root = REPO / '04-pure-r1-calculator/lean' if module == 'R1Calculator' or module.startswith('R1Calculator.') else FORMAL
    path = root / (module.replace('.', '/') + '.lean')
    return path if path.is_file() else None

def without_comments(text):
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

def import_closure(roots):
    local, external, visiting = set(), set(), set()
    def visit(module):
        if module in local: return
        assert module not in visiting, ('Circular import', module)
        path = source_for(module)
        if path is None:
            external.add(module); return
        visiting.add(module)
        text = without_comments(path.read_text())
        assert not re.search(r'\b(?:sorry|admit|native_decide)\b|^\s*(?:private\s+|public\s+)?axiom\b', text, re.M), module
        for line in IMPORT.findall(text):
            for dependency in line.split(): visit(dependency)
        visiting.remove(module); local.add(module)
    for root in roots: visit(root)
    return local, external

def statement_counts(register):
    counts = Counter()
    for paper in register['papers']:
        for statement in paper['statements']: counts[statement['status']] += 1
    return dict(counts, total=sum(counts.values()))

def verify(objects):
    encodings = load('EVIDENCE-ENCODINGS.json')
    evidence_files = {str(path.relative_to(HERE)) for path in HERE.rglob('*')
                      if path.is_file() and path.name != 'EVIDENCE-ENCODINGS.json'
                      and '__pycache__' not in path.parts}
    assert set(encodings) == evidence_files, 'Evidence index must cover every checkpoint file.'
    for name, info in encodings.items():
        raw = (HERE / name).read_bytes()
        decoded = gzip.decompress(raw) if info['encoding'] == 'gzip' else raw
        assert len(raw) == info['stored_bytes'] and sha(raw) == info['stored_sha256'], name
        assert len(decoded) == info['decoded_bytes'] and sha(decoded) == info['decoded_sha256'], name
    frozen = load('FROZEN-SPECS.json')
    archives = load('FROZEN-ARCHIVES.json') if (HERE / 'FROZEN-ARCHIVES.json').is_file() else {}
    for name, digest in frozen.items():
        assert sha((FORMAL / name).read_bytes()) == digest, name
        archive = HERE / archives.get(name, 'specifications/' + Path(name).name)
        assert sha(archive.read_bytes()) == digest, name
    if (HERE / 'PREFLIGHT-CORRECTIONS.json').is_file():
        for correction in load('PREFLIGHT-CORRECTIONS.json'):
            assert sha((HERE / correction['preserved_original']).read_bytes()) == correction['original_sha256']
            assert sha((FORMAL / correction['source']).read_bytes()) == correction['corrected_sha256']
    inherited = load('INHERITED-PINS.json.gz')
    for name, digest in inherited['sha256'].items():
        assert sha((REPO / name).read_bytes()) == digest, name

    accepted = load('ACCEPTANCE.json')
    assert accepted['status'] == 'accepted'
    assert accepted['base_commit'] == inherited['base_commit']
    assert accepted['native_profile'] == PROFILE
    assert not accepted['numbered_statement_promoted']
    assert not accepted['full_root_build_claimed'] and not accepted['remote_ci_claimed']
    register = json.loads((FORMAL / 'TARGETS.json').read_text())
    numbered = load('NUMBERED-STATUSES.json')
    assert numbered['base_commit'] == accepted['base_commit']
    assert numbered['statuses'] == {s['id']: s['status']
                                   for p in register['papers'] for s in p['statements']}
    assert accepted['numbered_register'] == statement_counts(register)
    pins = load('SOURCE-PINS.json.gz')
    local, external = import_closure(pins['gate_roots'] + pins['preflight_roots'])
    assert local == set(pins['modules'])
    assert external == set(pins['external_imports'])
    coverage = load('SOURCE-NATIVE-COVERAGE.json.gz')
    assert coverage['count'] == len(local) == accepted['source_matched_native_modules_including_preflights']
    assert {r['module'] for r in coverage['modules']} == local
    receipts = load('NATIVE-RECEIPTS.json.gz')
    logs = load('NATIVE-LOGS.json.gz')
    for receipt in receipts.values():
        for key, value in PROFILE.items(): assert receipt[key] == value
    for row in coverage['modules']:
        module = row['module']
        assert row['source'] == pins['modules'][module]
        assert sha((REPO / row['source']['path']).read_bytes()) == row['source']['sha256']
        native = row['native_row']
        assert native['source_sha256'] == row['source']['sha256']
        assert native['returncode'] == 0 and row['source_matched_success']
        assert native in receipts[row['receipt']]['modules']
        assert sha(logs[row['log']].encode()) == row['log_sha256']
        if objects:
            for artifact in row['artifacts']:
                path = REPO / artifact['path']
                assert path.stat().st_size == artifact['bytes'] and sha(path.read_bytes()) == artifact['sha256'], artifact['path']

    axioms = load('AXIOMS.json')
    assert set(axioms['allowed']) == ALLOWED
    assert axioms['exact_aliases'] == accepted['exact_aliases']
    for table in ['namespace_theorems', 'explicit_prints']:
        for name, used in axioms[table].items(): assert set(used) <= ALLOWED, (name, used)
    for name in axioms['exact_aliases']: assert name in axioms['explicit_prints'], name
    assert len(axioms['exact_aliases']) == accepted['exact_supporting_contracts']
    audited = set(axioms['namespace_theorems'])
    aliases = set(axioms['exact_aliases'])
    assert len(audited - aliases) == accepted['additional_namespace_declarations_audited']
    assert len(audited) == accepted['total_namespace_declarations_audited']
    assert len(audited & aliases) == accepted['exact_aliases_in_namespace_audits']
    print(json.dumps({'result': 'archived-evidence-and-current-source-consistent',
                      'new_native_build_performed': False, 'local_objects_checked': objects,
                      'frozen_files': len(frozen), 'inherited_files': len(inherited['sha256']),
                      'native_source_coverage': len(local), 'exact_contracts': len(axioms['exact_aliases']),
                      'numbered_register': accepted['numbered_register']}, indent=2))

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--native-objects', action='store_true', help='Also require and hash the matching local compiled artifacts.')
    verify(parser.parse_args().native_objects)
