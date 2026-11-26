#!/usr/bin/env python3
"""Root-only: turn one passing gate receipt into a native evidence file and a supporting record.

Usage: mk_record.py NUMBER SLUG PAPER RECEIPT_ID GATE_MODULE SOURCE_MAP SCOPE_FILE SRC.lean [SRC.lean ...]
Writes HOME/evidence/NUMBER-SLUG-native.json and accepted/NUMBER-SLUG.json. Refuses to overwrite.
Evidence used is exactly: one bounded native gate with named-axiom output, and a source-scope note.
"""
import sys, json, hashlib, re, subprocess
from pathlib import Path
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
REPO = ROOT.parent
num, slug, paper, rid, gate, smap, scopef, *srcs = sys.argv[1:]
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
rec = json.loads((ROOT / 'build-reports' / f'{rid}.json').read_text())
assert 'outcome' not in rec and all(m.get('returncode') == 0 for m in rec['modules']), 'receipt not clean'
row = [m for m in rec['modules'] if m['module'] == gate]
assert row, 'gate module not in receipt'
row = row[-1]
src_of = lambda m: ROOT / (m.replace('.', '/') + '.lean')
assert row['source_sha256'] == sha(src_of(gate)), 'gate source changed since receipt'
log = (ROOT / row['log']).read_text()
axioms = {}
for name, body in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log):
    axioms[name] = [a.strip() for a in body.replace('\n', ' ').split(',') if a.strip()]
assert axioms, 'no #print axioms output in gate log'
std = {'propext', 'Classical.choice', 'Quot.sound'}
assert all(set(v) <= std for v in axioms.values()), 'non-standard axiom'
assert 'sorryAx' not in log
head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=REPO, text=True).strip()
pins = {}
for s in srcs + [smap]:
    p = (ROOT / s).resolve()
    pins[str(p.relative_to(REPO))] = sha(p)
ev = {'status': 'checked', 'base_commit': head,
      'base_note': 'Sources are new files on top of this commit at gate time; root commits them afterwards.',
      'native_receipt': rid, 'native_receipt_sha256': sha(ROOT / 'build-reports' / f'{rid}.json'),
      'exact_gate': gate, 'gate_seconds': row.get('seconds'), 'gate_cpu_seconds': row.get('observed_cpu_seconds'),
      'peak_process_tree_rss_kib': row.get('peak_process_tree_rss_kib'),
      'named_axiom_output': axioms,
      'verification': 'One exact bounded Lean gate with focused source correspondence, no duplicate artifact replay.',
      'profile': {k: rec.get(k) for k in ['heap_cap_mib', 'rss_cap_mib', 'wall_seconds', 'cpu_seconds', 'minimum_free_mib', 'threads', 'upstream_cache_only']},
      'source_pins': pins}
evdir = HERE / 'evidence'; evdir.mkdir(exist_ok=True)
evp = evdir / f'{num}-{slug}-native.json'
accp = ROOT / 'verification/new-paper-set-2026-11-18/accepted' / f'{num}-{slug}.json'
assert not evp.exists() and not accp.exists(), 'refusing to overwrite'
evp.write_text(json.dumps(ev, indent=2) + '\n')
pins[str(evp.relative_to(REPO))] = sha(evp)
acc = {'id': f'new-set-{num}', 'kind': 'supporting only', 'paper': paper,
       'scope': Path(scopef).read_text().strip(),
       'evidence': '../local-fable-pair-2026-11-22-round3/evidence/' + evp.name, 'evidence_sha256': sha(evp),
       'statement_scope_check': '../local-fable-pair-2026-11-22-round3/' + str((ROOT / smap).resolve().relative_to(HERE)),
       'verification': 'Exact original native Lean normal profile and named axiom output, with source-to-statement scope checked by the authoring lane and root; no separate artifact replay, no cross-model review.',
       'native_receipt': rid, 'exact_alias_count': len(axioms), 'numbered_promotions': [], 'source_pins': pins}
accp.write_text(json.dumps(acc, indent=2) + '\n')
print('wrote', evp.relative_to(ROOT), 'and', accp.relative_to(ROOT), '| theorems:', len(axioms))
