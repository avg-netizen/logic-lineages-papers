# Semantic finite-coefficient vector consumer

This extends the checked recursor-free vector consumer of paper08 thm:finite-source to the complete semantic finite-coefficient scalar interface. It retains the original term code, canonical default assignment, shared ground-variable indices, actual zero-padded positive coordinates, and all three universal vector relations. WW-strict remains strict only at coordinate zero. Every recursor-free original term is proved to satisfy the new condition.

The condition finiteSource explicitly concerns every actual canonical extracted Scalar and requires all its fixed closed coefficients to have finite ordinal value. Actual extraction is guaranteed independently for original terms with ground free context. There is no assumed compiler success, BASE solver, or termination premise.

Boundary retained: the separate formal correspondence between this extracted-scalar condition and the printed condition on literal zeroth-coordinate source collapse nodes is not proved here. The full numbered theorem remains pending until that identification and promotion audit are complete. Existing accepted compilers and source files are unchanged.
