# Literal nat_omega_rec graph recursion, exact4
Mathlib/Computability/Primrec/List.lean nat_omega_rec' lines 312–360. The graph AST
starts at empty and at successor i builds exactly bindList(seed, m(seed)-i),
then filterMaps this frontier with each node's layer applied to mapGraph of the
SAME previous graph and literal dependencies. It replaces the old graph, does
not append to it, and preserves first-match lookup, missing omissions, order and
duplicates. Subtract is the existing counter-first Program: [i,m(seed)].

NativeGraph proves exact calibration for all indices, including above rank.
NativeCoherentGraph separately requires explicit native dependency decrease and
exact Some layer law and proves the original graph_eq_map_bindList invariant for
i <= m(seed)+1. Its coverage proof must justify lookup completeness; it may not
silently replace missing lookups by defaults. The rank and layer hypotheses are
ordinary native mathematics, not derivations inside ID1.

InternalZero and InternalSuccessor establish actual arithmetic graph equations
using actual R/subtract/bindList/stage graph hypotheses. They do not infer these
graphs or their semantic correctness from NativeGraph.

Still open: concrete original R/D/G supplier installation and internal semantic
correctness/coverage, recursive layer/headMove bridge to original exchange,
and original class coherence. This is faithful algorithm assembly, not a dense
row substitute and not a completed installed E. Existing tuple stays unchanged.
