# Literal dependency-frontier coverage: exact2

Source: Mathlib/Computability/Primrec/List.lean bindList repeated flatMap;
ExchangeFrontier.flattenStep/flatten/bindStep/bindList are the checked exact AST.
Flatten appends each node's dependencies before the flattened tail. No sorting,
deduplication, altered depth, or dense row construction is used.

Actual object-language membership in frontier, actual D graph, and actual child
membership in that dependency list imply membership in actual flatten output.
The successor theorem composes that fact with the checked actual bindList
successor equation, keeping symbolic depth and original parameter/seed.

Auxiliary dependencyMember is only an observation AST [child,node,param] used
to instantiate the paid RelationFold internal strong induction. Its graph is
constructed from actual D and contains graphs. Hit and tail preservation must
be proved using actual append membership; no generic supplier is left unpaid
at the exact endpoints. This reuses induction, not native reflection.

Global source-rank validity, previous-table answer correctness and independent
child/table coherence remain unpaid. No original recursive E completion claim.
Frozen awaiting independent review/preflight; no proof/compiler launched.
