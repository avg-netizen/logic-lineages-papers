# Move one actual cons head across a literal two-block partition

Exact root `LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountConsShiftProof`,
alias `exact_LiteralConsShift`. For actual chosen cons [head,left],
[head,right] and actual appends of cons(head,left) with right and left with
cons(head,right), give same literal occurrence comparison. Open both
swapped tails and the swapped second output by original append totality;
original append cons laws, exact swap, actual common head congruence and
comparator transitivity complete the move. Distinct from a filter, eraser,
signed occurrence split, or J.

243a4c48a7bb117da6225889279b08452153c7f19357042683eaecf1663fa54d  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalLiteralCountConsShiftProof.lean
