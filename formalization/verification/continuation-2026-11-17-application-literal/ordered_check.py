#!/usr/bin/env python3
"""Check one focused closure through the unchanged bounded native checker.

Dependency-first explicit roots avoid Python recursion depth in the original
scanner. This helper does not compile proofs itself or change the checker,
source restrictions, cache validation, locks, stop policy, or resource caps.
Use --list for a read-only closure summary.
"""

import hashlib
import importlib.util
import json
from pathlib import Path
import sys

ROOT = next(p for p in Path(__file__).resolve().parents
            if (p / 'scripts/check.py').is_file())
CHECKER = ROOT / 'scripts/check.py'
VERIFIER = ROOT / 'verification/continuation-2026-11-13/bounded-evidence-verifier/verify_evidence_bounded.py'
PINNED = {
    CHECKER: 'fefa8d645edc1c7bd1e4abc750cfaa6556adfc6cc80d6aecaff952192322a144',
    VERIFIER: '04bfb9d21762122b76b65f8eb4600fe925d1c75b6b3b6c5bb82358dba0683bff',
}


def load(name, path):
    if hashlib.sha256(path.read_bytes()).hexdigest() != PINNED[path]:
        raise RuntimeError('Changed checkpoint verification supplier: ' + str(path))
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


checker = load('fixed_checker', CHECKER)
verifier = load('fixed_verifier', VERIFIER)


def closure(roots):
    for root in roots:
        if checker.source_for(root) is None:
            raise ValueError('Missing requested local module: ' + root)
    seen, active, order, external = set(), set(), [], set()
    for root in roots:
        stack = [(root, False)]
        while stack:
            module, finish = stack.pop()
            if finish:
                active.remove(module)
                seen.add(module)
                order.append(module)
                continue
            if module in seen:
                continue
            if module in active:
                raise RuntimeError('Import cycle: ' + module)
            source = checker.source_for(module)
            if source is None:
                external.add(module)
                continue
            active.add(module)
            clean = verifier.clean_source(source.read_text())
            deps = [d for line in checker.IMPORT.findall(clean) for d in line.split()]
            stack.append((module, True))
            stack.extend((d, False) for d in reversed(deps))
    return order, sorted(external)


def main():
    args = sys.argv[1:]
    list_only = bool(args and args[0] == '--list')
    roots = args[1:] if list_only else args
    if not roots:
        raise SystemExit('At least one exact local module is required')
    order, external = closure(roots)
    summary = {
        'roots': roots,
        'local_modules': len(order),
        'external_imports': external,
        'existing_object_count': sum(
            (checker.BUILD / (m.replace('.', '/') + '.olean')).is_file()
            for m in order),
    }
    if list_only:
        print(json.dumps(summary, indent=2))
        return 0
    print('FOCUSED_CLOSURE ' + json.dumps(summary), flush=True)
    # The original checker still scans and validates every requested source.
    sys.argv = [str(CHECKER), '--memory-mib', '2048', '--rss-mib', '1536',
                '--min-free-mib', '2048', *order]
    return checker.main()


if __name__ == '__main__':
    raise SystemExit(main())
