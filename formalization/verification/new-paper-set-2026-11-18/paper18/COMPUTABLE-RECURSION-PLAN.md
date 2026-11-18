# Merely computable ranked recursion supplier

Supporting only. Existing literal partial compiler uses `Primrec.nat_omega_rec'`;
that is insufficient for arbitrary `PolicyShape.Effective p`, whose selector is
only Computable. Do not strengthen the policy assumption to primitive recursive.

Proposed exact supplier:
For Primcodable input/output types, a primitive recursive natural rank and
primitive recursive finite child list, a jointly Computable assembly returning
`Option output`, strict rank decrease for every actual child, and the literal
assembly equation `g b ((children b).map f) = some (f b)`, conclude Computable f.
The equation is the recursion specification, not a supplied computation oracle.
No restriction on changing other state parameters (partial grade may increase).

Construction follows the checked mathlib `Primrec.nat_omega_rec'` finite graph
algorithm: enumerate depth frontiers from the actual children, build successive
bottom-up result graphs, and look up the root. Replace ONLY the computability
proof of assembly-dependent finite traversals by genuine Computable nat recursion.
The number of rounds is rank(root)+1; child expansion is primitive recursive.
Graph correctness and termination follow strict rank, never assume success of
the numeric evaluator. Option failure remains in intermediate construction.

A separate supporting finite-list fold theorem permits a jointly Computable
step (not PR). Implement via Computable.nat_rec over list length and indexed
items, retaining original list order; derive map/filterMap as needed. Every
function is total for all encoded inputs.

This supplier alone is NOT policy partial recursion, abstraction, or full source
assignment. Next application must define actual policy-dependent assembly,
prove its joint computation using the selector, and prove literal partial syntax
calibration including whole-head-free precedence and all constructor/grade cases.
