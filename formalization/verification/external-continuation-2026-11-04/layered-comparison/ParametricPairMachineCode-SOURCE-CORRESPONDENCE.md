# Bounded indexed-control machine kernels

Target-only proposal. This is the bounded computation obligation toward paper09 hardness.tex lines316–319, using the already calibrated actual finite-pair worklist. It is not an upper-bound or total-collapse computability theorem.

The control family is the first-order map H : Nat×Nat→Nat. Its first coordinate is an index, not an encoding of an arbitrary function. ChildrenBudget takes an explicit numeric budget; the other kernels operate on standard Sum/Product/List state representations. Query reads the pending Eval pair norm and is zero otherwise. IndexedStep uses H only for this single numeric budget. Even malformed underflow and terminal states retain the original step semantics.

ExactCalibration identifies childrenBudget, indexedStep, indexedRun and indexedEvaluate with the unchanged actual children/step/run/evaluate at the section n↦H(i,n), for every state and fuel. KernelPrimitiveRecursive establishes the budget/stack operations independently of H. IndexedPrimitiveRecursive assumes Primrec H; IndexedComputable assumes only Computable H. Both conclusions are joint in all displayed numeric/index/state/fuel arguments, not merely pointwise assertions at fixed fuel.

No function-space Primcodable instance, runtime bound, primitive recursiveness of unbounded search, total collapse effectivity, gamma-family uniformity, complete source evaluator, upper bound, completeness or publication is claimed. Unbounded first-success search and actual total-value computability remain a separate step.
