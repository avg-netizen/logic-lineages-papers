#!/usr/bin/env python3
"""Root-side mechanical review of a lane B (Mathlib-profile) packet. Read-only.

Recomputes frozen pins, reproduces the recursive evidence compiler-free with
root_verify.py and compares it to the author's JSON, checks that pinned Lean
files are unchanged since they were first committed or untracked-new, and
scans the packet's audited Lean files for forbidden constructs.
Usage: root_review.py NAME PAPERDIR AUDIT_PREFIX   (e.g. RAW-PLAN-COMPILER paper19 LogicLineages.ControlSensitivityCurrent)
"""
import json, hashlib, pathlib, subprocess, sys, re, shutil, tempfile
HERE = pathlib.Path(__file__).resolve().parent; ROOT = HERE.parents[1]
name, paper, prefix = sys.argv[1:4]
P = ROOT / 'verification/new-paper-set-2026-11-18' / paper
def dg(p): return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
out = {'packet': name}
pins_file = next((P / f for f in (name + '-FROZEN-PINS.json', name + '-FREEZE.json', name + '-FROZEN.json') if (P / f).is_file()), None)
bad = []; n = 0
if pins_file:
    d = json.loads(pins_file.read_text()); pins = d.get('sources') or d.get('pins') or {}
    for k, v in pins.items():
        q = next((b / k for b in (ROOT, ROOT.parent, ROOT.parent / 'formalization') if (b / k).is_file()), None)
        n += 1
        if q is None or dg(q) != v: bad.append(k)
out['pins_file'] = pins_file.name if pins_file else None; out['pins'] = n; out['pin_mismatch'] = bad
ev = P / (name + '-EVIDENCE.json'); a = json.loads(ev.read_text())
tmp = pathlib.Path(tempfile.mkdtemp()) / 'e.json'
lean = shutil.which('lean'); pfx = subprocess.run([lean, '--print-prefix'], capture_output=True, text=True, cwd=ROOT).stdout.strip()
r = subprocess.run([sys.executable, str(HERE / 'root_verify.py'), *a['gates'], '--out', str(tmp), '--compiler', lean, '--compiler-prefix', pfx, '--audit-prefix', prefix], capture_output=True, text=True, cwd=ROOT)
b = json.loads(tmp.read_text()) if tmp.is_file() else {}
out.update(gates=a['gates'], reproduced_identical=(a == b), status=b.get('status'), modules=b.get('native_source_matched_modules'), errors=len(b.get('errors', [1])),
           aliases=len(b.get('new_named_standard_axioms', {})), evidence_sha256=dg(ev))
forb = re.compile(r'\b(unsafe|opaque|implemented_by|extern|partial|axiom|sorry|admit|native_decide)\b')
hits = []
for m, row in b.get('modules', {}).items():
    if prefix in m:
        text = pathlib.Path(row['source']).read_text()
        for i, line in enumerate(text.splitlines(), 1):
            if forb.search(line) and '#print axioms' not in line and not line.lstrip().startswith(('--', '/-')): hits.append(f'{m}:{i}')
out['forbidden_hits'] = hits[:5]
out['alias_names'] = sorted(k.rsplit('.', 1)[-1] for k in b.get('new_named_standard_axioms', {}))
print(json.dumps(out, indent=1))
