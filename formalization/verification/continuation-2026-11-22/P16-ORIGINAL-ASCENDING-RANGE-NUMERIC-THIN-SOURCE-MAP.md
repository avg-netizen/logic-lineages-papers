# Paper 16: exact numerical ordered original ascending range

The literal range here is the already frozen
`NumberedWindowInternalCoverAscendingRangeTargets.ascendingRange`.
At zero its output is standard scratch nil. At depth `n+1` it appends
the singleton `n` at the right of the actual predecessor list.
The numerical gate proves equality to the original ordered
`List.range` at every natural input, with its actual exact scratch codec.
It does not infer any open calculus proof from numerical calibration.

The older original range had its own checked numerical supplier. This
is a narrow recut for the physically identical selected grammar range,
using actual raw-list recursion and append evaluation, without the
historical broad source-head closure. The independently checked open
forward and backward range rules are separate. Grammar installation
and recursive stage transport are not part of this result.
