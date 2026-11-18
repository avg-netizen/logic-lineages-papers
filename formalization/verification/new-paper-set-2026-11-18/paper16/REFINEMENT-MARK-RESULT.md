# Successful marking reflection through actual refinement

Frozen RefinementMarkReflection passes native1794982980222064000-2 with
original core caps, unchanged definitions/targets and standard axioms only.
Recursive verifier reports28modules,one alias,zero errors.

Variables on the successfully marked right are impossible. Ordinary heads
become same-symbol marked heads with positionwise base witnesses and empty
extra witnesses; marked roots persist literally. Under lambdas, actual
one-free-variable opening commutes with partial marking even on failure, so
successful marking of the opened refining body reflects to its original body.
Actual typing/validity and fresh-name preservation build the new abstraction
refinement witness. The proof decreases the successful right mark's original
lambda-spine depth, which opening preserves; no refinement transitivity,
substitution closure or comparison cut is assumed.

Failed proof sources/receipts1794982936552451673-2 and1794982960460862202-2
retained. They attempted a generic sizeOf induction whose dependent tree
inequality did not discharge. Replaced by the explicit successful-spine
measure above, with its already-checked opening preservation theorem. This
is a proof-only change, not evidence of a checked general tree measure.

Supporting constituent only. Full refinement syntax, arbitrary renaming,
transitivity, two environments, full-call covariance, prefix escape and cut
remain pending. No numbered source lemma/root build/CI claim.
