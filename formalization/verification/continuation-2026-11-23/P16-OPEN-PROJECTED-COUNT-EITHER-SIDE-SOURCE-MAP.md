# Paper 16: exact occurrence cons step on either selected projection

If the literal projected head is retained on the left, use the
original append's cons equation and same-head literal count law.
If it is retained on the right, produce actual swapped append
reports before and after the cons via original object totality,
verify the same count equality by the exact literal swap law,
apply the left case, and finally restore original append order.

Exact gate: NumberedWindowInternalProjectedCountEitherSideProof,
aliases exact_ProjectedCountOnLeft and exact_ProjectedCountOnRight.
No arithmetic case oracle remains. All list and observer reports
use the original physical graphs. This discharges the arithmetic
supplier for the simultaneous projections; the list induction and
certificate rebuilding are still separate.

Frozen Lean source hashes (SHA-256):

    85aac08a7dd185b8db701251cdd37e438a7e2b3858621d344993baf5b7e4a463  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalProjectedCountEitherSideProof.lean
