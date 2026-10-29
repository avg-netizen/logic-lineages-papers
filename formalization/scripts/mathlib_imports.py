#!/usr/bin/env python3
"""List Mathlib cache roots used by the accepted local source import closure."""
from __future__ import annotations

import sys
from check import IMPORT, source_for

seen: set[str] = set()
upstream: set[str] = set()


def visit(module: str) -> None:
    if module in seen:
        return
    seen.add(module)
    source = source_for(module)
    if source is None:
        return
    text = source.read_text()
    # Ignore nested block comments and line comments before reading imports.
    code, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith('/-', i):
            depth += 1
            code.append('  ')
            i += 2
        elif depth and text.startswith('-/', i):
            depth -= 1
            code.append('  ')
            i += 2
        elif not depth and text.startswith('--', i):
            end = text.find('\n', i)
            if end < 0:
                break
            code.append('\n')
            i = end + 1
        else:
            code.append(text[i] if not depth or text[i] == '\n' else ' ')
            i += 1
    for line in IMPORT.findall(''.join(code)):
        for dependency in line.split():
            if dependency == 'Mathlib' or dependency.startswith('Mathlib.'):
                upstream.add(dependency)
            else:
                visit(dependency)


for root in sys.argv[1:] or ['LogicLineages']:
    visit(root)
print('\n'.join(sorted(upstream)))
