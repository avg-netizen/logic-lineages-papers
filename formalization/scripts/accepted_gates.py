#!/usr/bin/env python3
"""List the accepted component gates selected by the public root module."""
from check import IMPORT, ROOT

gates = [name for line in IMPORT.findall((ROOT / 'LogicLineages.lean').read_text())
         for name in line.split()
         if name.startswith('LogicLineages.') and name != 'LogicLineages.Audit']
if not gates:
    raise SystemExit('The accepted root selects no component gates.')
print('\n'.join(dict.fromkeys(gates)))
