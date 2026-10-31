#!/usr/bin/env python3
"""One bounded exact control of the cotree repair, with no Lean or network."""
from __future__ import annotations

import argparse
import fcntl
import hashlib
import json
from pathlib import Path
import resource
import signal
import time

from cotrees import (Leaf, Node, binary_expressions, evaluated_graph, is_reduced,
                     leaf_names, restrict, shape, topologically_embeds)


def verify(max_leaves):
    started = time.monotonic()
    expressions = subsets = 0
    for size in range(1, max_leaves + 1):
        for tree in binary_expressions(size):
            expressions += 1
            vertices, edges = evaluated_graph(tree)
            for mask in range(1 << size):
                selected = frozenset(i for i in range(size) if mask & (1 << i))
                result = restrict(tree, selected)
                assert is_reduced(result)
                assert leaf_names(result) == selected
                assert evaluated_graph(result) == (
                    selected, frozenset((a, b) for a, b in edges
                                        if a in selected and b in selected))
                assert restrict(result, selected) == result
                subsets += 1

    a, b, c, d = (Leaf(i) for i in range(4))
    i3 = Node(0, (a, c, d))
    isolated_p3 = Node(0, (a, Node(1, (b, Node(0, (c, d))))))
    assert evaluated_graph(i3)[1] == frozenset()
    assert evaluated_graph(isolated_p3)[1] == frozenset([(1, 2), (1, 3)])
    assert shape(restrict(isolated_p3, frozenset([0, 2, 3]))) == shape(i3)
    assert not topologically_embeds(i3, isolated_p3)

    isolated_edge = Node(0, (a, Node(1, (b, c))))
    wrongly_contracted = Node(0, (a, b, c))
    assert evaluated_graph(isolated_edge)[1] == frozenset([(1, 2)])
    assert evaluated_graph(wrongly_contracted)[1] == frozenset()
    assert restrict(isolated_edge, frozenset([0, 1, 2])) == isolated_edge

    balanced = Node(0, (Node(0, (a, b)), Node(0, (c, d))))
    comb = Node(0, (a, Node(0, (b, Node(0, (c, d))))))
    assert evaluated_graph(balanced) == evaluated_graph(comb)
    assert shape(restrict(balanced, frozenset(range(4)))) == shape(
        restrict(comb, frozenset(range(4))))
    assert not any(topologically_embeds(balanced, host)
                   and topologically_embeds(comb, host)
                   for n in range(1, 5) for host in binary_expressions(n))
    return {'outcome': 'PASS', 'max_leaves': max_leaves,
            'binary_expressions_checked': expressions,
            'literal_leaf_restrictions_checked': subsets,
            'fixtures': ['I3 in isolated-P3: correct restriction, failed strict topology',
                         'isolated-edge: reject different-operator contraction',
                         'I0..I4: graph JEP does not imply binary-parse topological JEP'],
            'elapsed_seconds': time.monotonic() - started,
            'maximum_rss_kib': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
            'scope': 'Bounded semantic controls, not a proof of general JEP decidability'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-leaves', type=int, default=6)
    parser.add_argument('--report', type=Path, required=True)
    args = parser.parse_args()
    if not 1 <= args.max_leaves <= 6:
        parser.error('This fixed control is capped at six leaves')
    available = next(int(line.split()[1]) for line in Path('/proc/meminfo').read_text().splitlines()
                     if line.startswith('MemAvailable:'))
    if available < 1536 * 1024:
        raise SystemExit('Insufficient memory headroom; no test launched')
    resource.setrlimit(resource.RLIMIT_AS, (512 * 1024**2, 512 * 1024**2))
    resource.setrlimit(resource.RLIMIT_CPU, (60, 60))
    with Path('/tmp/logic-lineages-ii5-reverse-compute.lock').open('a') as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            raise SystemExit('COMPUTE_BUSY: another bounded scientific control is active')
        signal.alarm(60)  # Independent wall-clock cap, in addition to CPU/AS limits.
        try:
            result = verify(args.max_leaves)
        finally:
            signal.alarm(0)
    here = Path(__file__).resolve().parent
    result['source_hashes'] = {name: hashlib.sha256((here / name).read_bytes()).hexdigest()
                               for name in ('cotrees.py', 'verify_restriction.py')}
    args.report.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result))


if __name__ == '__main__':
    main()
