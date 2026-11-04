# Bounded halving trace and exact existing binary DAG

This is a literal constructor identity supplier for the binary coefficient construction used in paper09 hardness.tex lines 294–314. It does not assert source hardness or a complexity bound.

The existing SourceAdditionCompletion.binaryDAG uses well-founded recursion on k/2 with zero/one base cases, double for even k and doubleOne for odd k. The new numeric trace uses exactly k finite advances, stuttering when the current number is less than two. Each genuine advance prepends current n%2 to the accumulated list and replaces n by n/2.

ExactTerminalTrace proves that the final number is zero or one, every recorded bit is zero or one, and terminal zero occurs exactly when original k=0. ExactReconstruction folds the recorded bits left-to-right around the exact terminal zero/one DAG. Prepending while descending makes the final list inner-to-outer; the target is equality with the actual existing binaryDAG k, not just equal interpreted values.

UniformPrimitiveRecursive covers advance and trace on all raw natural/list states, using division/modulo by two, list cons and finite iteration. The explicit generous k fuel is not a logarithmic runtime claim. No primitive-recursive instance for abstract BinaryDAG is presumed; PR is asserted only for the numeric trace. Numeric CPS binaryPlan transport, binder allocation, complete (b,e)-to-spine construction, scalar Nat wrapper and source size/runtime remain separate obligations.

No accepted/frozen files change; verification-only, no export.
