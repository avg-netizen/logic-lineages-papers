# Independent finite-profile pre-scope review

All four frozen pins match. Approved for proof development as a supporting
packet, not full prop:equal-gap. Read actual RelativeNorm, raw comparison/norm
code and current entries.tex finite joint-profile calculation.

RawProfileCode is a genuine total course-of-values table: code n+1 decodes
its exponent/coefficient/tail from n; comparison code 2 means query exponent
strictly exceeds the head, hence only that coefficient weight is omitted.
It always recursively retains the filtered tail. Correctness is explicitly
against actualOrdinalNorm of the actual ordinary filtered CNF prefix, not a
new semantics defined to equal the code. PR on all raw inputs is separate
from source interpretation on normal notations.

SameProfilePiece retains the inclusive query<=breakpoint condition, so both
actual filters, and therefore actual norms, must agree. The finite cover
includes 2, every breakpoint, every breakpoint successor, filtered by [2,E).
Duplicates, shared breakpoints, exact right endpoints, empty prefixes, and
E<=2 are retained. E and both prefixes remain below epsilonZero.

Proof detail: if using the greatest breakpoint b<x, choose max(2,b+1),
not unconditionally b+1; b=0 with x>=2 otherwise produces an excluded
representative. If this max is 2 use the explicit 2 representative; otherwise
use the successor entry. If no strict lower breakpoint, 2 has the same piece.
This is a proof obligation only, not a necessary definition/target change.

The packet deliberately does not claim a computable representative list,
highest-piece selector, actual phase visits/no-skip, effective sufficient tail,
or eventual comparison. Those remain necessary for full equal-gap.
