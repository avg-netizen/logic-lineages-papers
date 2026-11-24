#!/usr/bin/env python3
"""List Mathlib cache roots used by the accepted local source import closure."""
from __future__ import annotations

import sys
from check import IMPORT, dependency_postorder, source_for, strip_lean_comments


def collect_mathlib_imports(roots: list[str]) -> list[str]:
    upstream: set[str] = set()

    def local_children(module: str) -> list[str]:
        source = source_for(module)
        if source is None:
            return []
        children = []
        for line in IMPORT.findall(strip_lean_comments(source.read_text())):
            for dependency in line.split():
                if dependency == 'Mathlib' or dependency.startswith('Mathlib.'):
                    upstream.add(dependency)
                else:
                    children.append(dependency)
        return children

    for _ in dependency_postorder(roots, local_children):
        pass
    return sorted(upstream)


if __name__ == '__main__':
    print('\n'.join(collect_mathlib_imports(sys.argv[1:] or ['LogicLineages'])))
