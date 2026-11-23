# Exact literal occurrence counts at actual append nil/cons
The nil report is forced by append functionality; the literal empty
counter returns zero. For cons, the given actual append reports reconstruct
the same head at the joined output. For head equal to the needle, both
actual counts go up one and internal PA left-successor addition computes
the new sum. For unequal head, both remain unchanged. This pays one
genuine append constructor at actual held tail reports and count sum,
not yet the object induction over arbitrary front tapes.
