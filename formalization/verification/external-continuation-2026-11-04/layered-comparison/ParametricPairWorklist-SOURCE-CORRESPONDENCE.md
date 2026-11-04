# Finite-pair worklist execution and first success

Target-only proposal. Paper09 hardness.tex lines316–319 requires an effective finite-head collapse evaluator for its upper-bound argument. This component pays the termination and actual-value calibration obligations of a concrete first-order worklist machine, not its effectivity certificate.

The predecessor list has explicit row-major ordering and no duplicates; its underlying finset is exactly the previously proved actual bounded-predecessor set. Eval tasks expand that list followed by a Combine task with the exact child count. Child values accumulate on the value stack in reverse processing order; Combine uses the order-independent maximum of each child value plus one. Zero children produce zero, exactly the empty maximum. Underflow is explicitly stuck on malformed states, never used by the correct-execution proof.

ContinuationCalibration is quantified over arbitrary task continuation and arbitrary pre-existing value stack, not just an empty run. It gives a finite exact execution segment that consumes only the evaluated task and pushes its actual collapseWith value. A lexicographically smaller-pair induction must establish this, with child list sequencing and stack arity proved.

ExactSuccess states that every observed singleton terminal result is the actual value, that some finite fuel succeeds, and that the least successful fuel exists with every earlier result None. This uses the existing Nat.rfind semantics, not a default value substituted for nontermination. G is arbitrary; no monotonicity, majorization or computability hypothesis is assumed.

No PR/computability, numeric encoding, runtime bound, complete source evaluator, upper bound, completeness or publication claim. All existing assignments, collapse definitions and manuscripts remain unchanged.
