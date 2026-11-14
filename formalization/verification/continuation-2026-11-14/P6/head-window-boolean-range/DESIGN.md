# Actual Boolean range and source-window guard, exact3

Original headMove (NumberedExchangeCode.headMove, guards 25–33) checks window
on source f but sourceHeads membership on target g. Source window alone cannot
replace target membership. We preserve both, instead proving that actual target
sourceHeads membership implies the actual target window acceptance.

The paid SourceHeadsFilterAdequacy gives nonzero queried window output, NOT
output=1. This packet pays the missing range internally: actual contains numeric
list recursion gives output=0 or output=1 by arithmetic strong induction; actual
window composition and branch AST preserve that disjunction for all raw inputs,
including invalid tag zero defaults and arbitrary arity-table outputs. Then
sourceHeads membership plus the paid filter law excludes zero and yields one.
Both raw enumeration and window outputs are internal totality witnesses eliminated
with programCases; no semantic witness extraction or supplier premises.

No native calibration is used as internal correctness. No typed validity,
SubtypeClosed discharge, source-target window transport, full headMove semantics,
or original recursive E correctness is claimed. Literal ASTs/order/duplicates
unchanged. BooleanValue is actual arithmetic disjunction, not metalevel split.
