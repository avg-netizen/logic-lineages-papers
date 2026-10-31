"""Finite reference model for the cotree restriction repair.

Leaf names are graph vertices. Internal nodes are disjoint union (0) or
join (1). The implementation keeps the chosen vertex set literally; it
does not replace induced graph embeddings by topological tree embeddings.
This is an executable mathematical control, not a JEP decision algorithm.
"""
from __future__ import annotations

from dataclasses import dataclass
from functools import lru_cache
from itertools import permutations


@dataclass(frozen=True)
class Leaf:
    name: int


@dataclass(frozen=True)
class Node:
    label: int
    children: tuple["Tree", ...]

    def __post_init__(self):
        if self.label not in (0, 1) or len(self.children) < 2:
            raise ValueError("A constructor has label 0/1 and at least two children")


Tree = Leaf | Node
OptionalTree = Tree | None


def leaf_names(tree: OptionalTree) -> frozenset[int]:
    if tree is None:
        return frozenset()
    if isinstance(tree, Leaf):
        return frozenset([tree.name])
    names = [leaf_names(child) for child in tree.children]
    if sum(map(len, names)) != len(frozenset().union(*names)):
        raise ValueError("Leaf names must be distinct")
    return frozenset().union(*names)


def evaluated_graph(tree: OptionalTree):
    """Evaluate constructors directly, without any pruning/normalization."""
    if tree is None:
        return frozenset(), frozenset()
    if isinstance(tree, Leaf):
        return frozenset([tree.name]), frozenset()
    parts = [evaluated_graph(child) for child in tree.children]
    vertices = frozenset().union(*(v for v, _ in parts))
    if sum(len(v) for v, _ in parts) != len(vertices):
        raise ValueError("Leaf names must be distinct")
    edges = set().union(*(e for _, e in parts))
    if tree.label:
        for i, (left, _) in enumerate(parts):
            for right, _ in parts[i + 1:]:
                edges.update(tuple(sorted((a, b))) for a in left for b in right)
    return vertices, frozenset(edges)


def assemble(label: int, children: tuple[OptionalTree, ...]) -> OptionalTree:
    """Remove empties, suppress unary nodes, flatten ONLY the same operator."""
    retained = tuple(child for child in children if child is not None)
    if not retained:
        return None
    if len(retained) == 1:
        return retained[0]
    flat = []
    for child in retained:
        if isinstance(child, Node) and child.label == label:
            flat.extend(child.children)
        else:
            flat.append(child)
    return Node(label, tuple(flat))


def restrict(tree: OptionalTree, selected: frozenset[int]) -> OptionalTree:
    if tree is None:
        return None
    if isinstance(tree, Leaf):
        return tree if tree.name in selected else None
    return assemble(tree.label, tuple(restrict(child, selected) for child in tree.children))


def is_reduced(tree: OptionalTree) -> bool:
    if tree is None or isinstance(tree, Leaf):
        return True
    return all(is_reduced(child) and not (
        isinstance(child, Node) and child.label == tree.label
    ) for child in tree.children)


def shape(tree: OptionalTree):
    """Unordered operator-labeled isomorphism type, forgetting vertex names."""
    if tree is None:
        return ()
    if isinstance(tree, Leaf):
        return (2,)
    return (tree.label, tuple(sorted(shape(child) for child in tree.children)))


@lru_cache(None)
def topologically_embeds(source: Tree, target: Tree) -> bool:
    """The strict label-preserving, downward edge-disjoint reading, for controls.

    Children use distinct target branches. Internal/leaf labels are preserved;
    the source root may land below the target root. This is intentionally NOT
    the repaired cotree restriction order.
    """
    if isinstance(source, Leaf):
        return True  # every nonempty finite tree has a leaf
    if isinstance(target, Leaf):
        return False
    if source.label == target.label and len(source.children) <= len(target.children):
        for chosen in permutations(target.children, len(source.children)):
            if all(topologically_embeds(s, t) for s, t in zip(source.children, chosen)):
                return True
    return any(topologically_embeds(source, child) for child in target.children)


def binary_expressions(leaves: int, start: int = 0):
    """Every ordered full binary 0/1 parse with this many distinct leaves."""
    if leaves == 1:
        yield Leaf(start)
        return
    for left_size in range(1, leaves):
        for left in binary_expressions(left_size, start):
            for right in binary_expressions(leaves - left_size, start + left_size):
                for label in (0, 1):
                    yield Node(label, (left, right))
