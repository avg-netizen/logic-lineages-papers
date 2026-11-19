#!/usr/bin/env python3
"""Add-only Nov19 review variant recognizing Lean axiom-free audit lines.
Original checker and original review script remain unchanged.

Root-side mechanical review of a lane A (core-profile) packet. Read-only.

Starting from the acceptance-schema evidence, independently checks the on-disk
state: source and object hashes, the checker's own .checked.json record for
every module (passing native row, core profile, same input key, row present in
its receipt), log hashes, source pins, and re-reads the axiom lines from the
native logs. Usage: root_review_core.py paper16/NAME-EVIDENCE.json
"""
import json, hashlib, pathlib, re, sys
HERE = pathlib.Path(__file__).resolve().parent; ROOT = HERE.parents[2]; REPO = ROOT.parent
ev = ROOT / 'verification/new-paper-set-2026-11-18' / sys.argv[1]
d = json.loads(ev.read_text())
def dg(p):
    p = pathlib.Path(p); return hashlib.sha256(p.read_bytes()).hexdigest() if p.is_file() else None
CORE = {"heap_cap_mib": 1536, "rss_cap_mib": 512, "wall_seconds": 180, "cpu_seconds": 90, "minimum_free_mib": 768,
        "core_only_profile": True, "single_thread": True, "threads": 1, "upstream_cache_only": True}
STD = {'propext', 'Classical.choice', 'Quot.sound'}
errs = []; axioms = {}
forb = re.compile(r'\b(unsafe|opaque|implemented_by|extern|partial|axiom|sorry|admit|native_decide)\b')
for m in d['modules']:
    n = m['module']
    try:
        src = ROOT / (n.replace('.', '/') + '.lean'); obj = ROOT / '.lake/build/lib/lean' / (n.replace('.', '/') + '.olean')
        assert dg(src) == m['source_sha256'], 'source'
        for fn, h in m['outputs'].items(): assert dg(fn) == h, 'output ' + fn
        e = json.loads(obj.with_suffix('.checked.json').read_text()); row = e['native_row']
        assert row['returncode'] == 0 and row['module'] == n and row['source_sha256'] == m['source_sha256'], 'native row'
        assert e['native_profile'] == CORE, 'profile'
        assert e['input_key'] == m['input_key'], 'input key'
        rc = json.loads(pathlib.Path(e['native_receipt']).read_text()); assert row in rc['modules'], 'row not in receipt'
        log = ROOT / row['log']; assert dg(log) == e['log_sha256'] == m['log_sha256'], 'log'
        text = log.read_text()
        assert not re.search(r'error:|sorry', text), 'log error'
        for name, axs in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text):
            axioms[name] = [x.strip() for x in axs.split(',') if x.strip()]
        for name in re.findall(r"'([^']+)' does not depend on any axioms", text):
            axioms[name] = []
        # Strip nested Lean block comments while preserving newline numbers.
        # Continuation prose such as "partial symbolic" is not a declaration.
        raw = src.read_text(); out = []; pos = 0; depth = 0
        while pos < len(raw):
            if raw.startswith('/-', pos):
                depth += 1; out.extend('  '); pos += 2
            elif depth and raw.startswith('-/', pos):
                depth -= 1; out.extend('  '); pos += 2
            elif depth:
                out.append('\n' if raw[pos] == '\n' else ' '); pos += 1
            else:
                out.append(raw[pos]); pos += 1
        assert depth == 0, 'unclosed block comment'
        code = ''.join(out)
        for i, line in enumerate(code.splitlines(), 1):
            if forb.search(line) and '#print axioms' not in line and not line.lstrip().startswith(('--', '/-')):
                errs.append(f'forbidden {n}:{i}')
    except (AssertionError, OSError, KeyError, ValueError) as x:
        errs.append(f'{n}: {x}')
for k, v in d['source_pins'].items():
    if dg(REPO / k) != v: errs.append('pin ' + k)
for k, v in d['axioms'].items():
    if axioms.get(k) != v or set(v) - STD: errs.append('axiom ' + k)
print(json.dumps({'evidence': sys.argv[1], 'evidence_sha256': dg(ev), 'modules': len(d['modules']), 'pins': len(d['source_pins']),
                  'aliases': sorted(k.rsplit('.', 1)[-1] for k in d['axioms']), 'errors': errs[:8], 'gate': pathlib.Path(d['gate']).stem}, indent=1))

if errs:
    sys.exit(1)
