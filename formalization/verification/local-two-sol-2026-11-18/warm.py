#!/usr/bin/env python3
"""Background cache warmer: replays existing sources through scripts/check.py.

Nothing is accepted or claimed by warming; it only populates the local
content-verified .olean cache (the 2026-11-18 work was compiled on another
machine, so none of its objects exist here). Small batches, and it yields
whenever a gate.sh caller is waiting. Failures are logged and skipped.
Usage: warm.py [--batch N] DIR_OR_MODULE...
"""
import subprocess, sys, time, json, os
from pathlib import Path
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(HERE))
import import_graph as g
PROFILE = {'core': ['--core-profile'],
           'mathlib': ['--memory-mib', '2048', '--rss-mib', '1536', '--min-free-mib', '2048']}
args = sys.argv[1:]; batch = 12
if args[:1] == ['--batch']: batch = int(args[1]); args = args[2:]
mods = [m for a in args for m in g.modules_under(a)]
order = g.closure(mods)
log = (HERE / 'logs' / 'warm.log').open('a')
def say(*a):
    print(time.strftime('%H:%M:%S'), *a, file=log, flush=True)
def cached(m):
    t = ROOT / '.lake/build/lib/lean' / (m.replace('.', '/') + '.olean')
    return t.is_file() and t.with_suffix('.checked.json').is_file()
def waiting():
    now = time.time()
    return any(now - f.stat().st_mtime < 120 for f in (HERE / 'logs').glob('gate-waiting.*'))
bad = set(); todo = [m for m in order if not m.startswith('R1Calculator')]
say('start', len(todo), 'modules, batch', batch)
i = 0
while i < len(todo):
    if (HERE / 'logs' / 'WARM-STOP').exists(): say('stop flag'); break
    chunk = []
    while i < len(todo) and len(chunk) < batch:
        m = todo[i]; i += 1
        if cached(m) or m in bad: continue
        if any(d in bad for d in g.closure([m])): bad.add(m); continue
        if chunk and g.is_core(m) != g.is_core(chunk[0]): i -= 1; break
        chunk.append(m)
    if not chunk: continue
    while waiting(): time.sleep(2)
    prof = 'core' if g.is_core(chunk[0]) else 'mathlib'
    while True:
        r = subprocess.run([sys.executable, 'scripts/check.py', *PROFILE[prof], *chunk],
                           cwd=ROOT, capture_output=True, text=True)
        if r.returncode in (75, 76): time.sleep(5 if r.returncode == 75 else 30); continue
        break
    if r.returncode == 78: say('scheduled stop'); break
    if r.returncode:
        failed = [l.split()[1].rstrip(':') for l in r.stdout.splitlines() if l.startswith('COMPILE_FAILED')]
        say('FAIL rc', r.returncode, failed or chunk[-1:])
        if failed: bad.update(failed); i -= len(chunk)   # retry the rest of the chunk without it
        else: bad.update(chunk)
    else:
        say('ok', prof, len(chunk), chunk[-1], 'at', i, '/', len(todo))
say('done; failed:', sorted(bad))
