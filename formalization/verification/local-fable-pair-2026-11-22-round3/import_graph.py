#!/usr/bin/env python3
"""Local import graph of the formalization tree (read-only helper).

Usage: import_graph.py summary | closure MODULE | order DIR_OR_MODULE...
Parses imports exactly as scripts/check.py does (comments stripped).
"""
import re, sys, json, collections
from pathlib import Path
ROOT = Path(__file__).resolve().parents[2]
CALC = ROOT.parent / "04-pure-r1-calculator/lean"
IMPORT = re.compile(r"^\s*(?:(?:public|private|meta)\s+)*import\s+(.+)$", re.M)
def src(m):
    base = CALC if (m == "R1Calculator" or m.startswith("R1Calculator.")) else ROOT
    p = base / (m.replace(".", "/") + ".lean")
    return p if p.is_file() else None
def strip(text):
    code, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith('/-', i): depth += 1; code.append('  '); i += 2
        elif depth and text.startswith('-/', i): depth -= 1; code.append('  '); i += 2
        elif not depth and text.startswith('--', i):
            end = text.find('\n', i)
            if end < 0: break
            code.append('\n'); i = end + 1
        else: code.append(text[i] if not depth or text[i] == '\n' else ' '); i += 1
    return ''.join(code)
_cache = {}
def imports(m):
    if m not in _cache:
        loc, ext = [], []
        for line in IMPORT.findall(strip(src(m).read_text())):
            for d in line.split():
                (loc if src(d) is not None else ext).append(d)
        _cache[m] = (loc, ext)
    return _cache[m]
def closure(mods):
    order, seen = [], set()
    def visit(m):
        if m in seen: return
        seen.add(m)
        for d in imports(m)[0]: visit(d)
        order.append(m)
    sys.setrecursionlimit(100000)
    for m in mods: visit(m)
    return order
def is_core(m, memo={}):
    if m not in memo:
        loc, ext = imports(m)
        ok = all(e.split('.')[0] in ('Init', 'Lean', 'Std') for e in ext) and not m.startswith('R1Calculator')
        memo[m] = ok and all(is_core(d) for d in loc)
    return memo[m]
def modules_under(arg):
    p = ROOT / arg
    if p.is_dir():
        return sorted(str(f.relative_to(ROOT).with_suffix('')).replace('/', '.') for f in p.rglob('*.lean'))
    return [arg.replace('/', '.').removesuffix('.lean')]
if __name__ == '__main__':
    cmd = sys.argv[1]
    if cmd == 'summary':
        for d in sys.argv[2:]:
            ms = modules_under(d)
            core = sum(is_core(m) for m in ms)
            cross = collections.Counter()
            for m in ms:
                for x in closure([m]):
                    top = '.'.join(x.split('.')[:2])
                    if not x.startswith(d.replace('/', '.')): cross[top] += 1
            print(d, 'modules', len(ms), 'core-only', core, 'non-core', len(ms) - core, 'outside-closure-tops', dict(cross.most_common(6)))
    elif cmd == 'closure':
        for m in closure(modules_under(sys.argv[2])): print(m, 'core' if is_core(m) else 'mathlib')
    elif cmd == 'order':
        ms = [m for a in sys.argv[2:] for m in modules_under(a)]
        for m in closure(ms): print(m, 'core' if is_core(m) else 'mathlib')
