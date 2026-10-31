#!/usr/bin/env python3
"""Bounded exact control of AC saturation, using nonassociative automata.

The two sides are independent finite calculations: direct automaton evaluation
on every ordered binary parse versus bottom-up multiset parsing of reduced
cotrees. This checks a decision-proof lemma, not general algorithm termination.
"""
from __future__ import annotations

import argparse
from collections import defaultdict
from functools import cache
import fcntl
import hashlib
import json
from pathlib import Path
import resource
import signal
import time

from cotrees import Leaf, binary_expressions, leaf_names, restrict, shape


def parse_state(tree, transition):
    if isinstance(tree, Leaf):
        return 0
    left, right = tree.children
    return transition(tree.label, parse_state(left, transition),
                      parse_state(right, transition))


def multiset_states(operator, children, transition):
    """All CFG derivations on the literal multiset of child-state sets.

    Occurrences remain distinct even when their state sets coincide. Ordered
    bipartitions account for every permutation and binary association; the
    original transition itself is never assumed commutative or associative.
    """
    size = len(children)
    possible = {1 << i: states for i, states in enumerate(children)}
    for mask in range(1, 1 << size):
        if mask in possible:
            continue
        reached = set()
        left = (mask - 1) & mask
        while left:
            right = mask ^ left
            if right:
                reached.update(transition(operator, x, y)
                               for x in possible[left] for y in possible[right])
            left = (left - 1) & mask
        possible[mask] = frozenset(reached)
    return possible[(1 << size) - 1]


def canonical_evaluator(transition):
    @cache
    def evaluate(cotree_shape):
        if cotree_shape == (2,):
            return frozenset([0])
        operator, child_shapes = cotree_shape
        return multiset_states(operator, tuple(evaluate(child) for child in child_shapes),
                               transition)
    return evaluate


def verify():
    started = time.monotonic()
    # Every ordered binary 0/1 parse through six leaves is generated once.
    cases = [(n, t, shape(restrict(t, leaf_names(t))))
             for n in range(1, 7) for t in binary_expressions(n)]
    comparisons = binary_evaluations = models = 0

    def compare(transition, bound):
        nonlocal comparisons, binary_evaluations, models
        direct = defaultdict(set)
        for n, tree, canonical in cases:
            if n <= bound:
                direct[canonical].add(parse_state(tree, transition))
                binary_evaluations += 1
        evaluate = canonical_evaluator(transition)
        for canonical, states in direct.items():
            assert evaluate(canonical) == frozenset(states), (canonical, states)
            comparisons += 1
        models += 1

    # Exhaust EVERY pair of binary transitions on two states, leaf state 0.
    for table in range(256):
        def transition(operator, left, right, table=table):
            return (table >> (4 * operator + 2 * left + right)) & 1
        compare(transition, 5)

    # Three larger examples also use every six-leaf ordered parse.
    for seed in range(3):
        def transition(operator, left, right, seed=seed):
            return (left + 2 * right + operator + seed + left * right) % 3
        compare(transition, 6)

    # An explicitly nonassociative transition must retain BOTH outcomes.
    nand = lambda operator, left, right: int(not (left and right))
    four_leaves = (0, ((2,), (2,), (2,), (2,)))
    assert canonical_evaluator(nand)(four_leaves) == frozenset([0, 1])

    # Equal children are a MULTISET: four leaves may not be deduplicated.
    add_capped = lambda operator, left, right: min(5, left + right)
    assert multiset_states(0, (frozenset([1]),) * 4, add_capped) == frozenset([4])

    # Ordered transitions require accounting for child permutations too.
    order_sensitive = lambda operator, left, right: (
        int(not (left and right)) if operator == 0 else left)
    edge_plus_leaf = (1, ((2,), (0, ((2,), (2,)))))
    assert canonical_evaluator(order_sensitive)(edge_plus_leaf) == frozenset([0, 1])

    return dict(outcome='PASS', models=models,
                exhaustive_two_state_transition_pairs=256,
                maximum_leaves_for_exhaustive_models=5,
                maximum_leaves_for_three_state_models=6,
                direct_ordered_binary_evaluations=binary_evaluations,
                exact_canonical_state_set_comparisons=comparisons,
                fixtures=['nonassociativity retains multiple reachable states',
                          'identical children retain their multiplicities',
                          'noncommutative transitions account for permutations'],
                elapsed_seconds=time.monotonic() - started,
                maximum_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
                scope='Finite controls of the AC-state lemma; not a JEP implementation')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--report', type=Path, required=True)
    args = parser.parse_args()
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
        signal.alarm(60)
        try:
            result = verify()
        finally:
            signal.alarm(0)
    here = Path(__file__).resolve().parent
    result['source_hashes'] = {name: hashlib.sha256((here / name).read_bytes()).hexdigest()
                               for name in ('cotrees.py', 'verify_ac_states.py')}
    args.report.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result))


if __name__ == '__main__':
    main()
