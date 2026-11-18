# Independent conceptual review: actual ordinal endpoint programs

Approved direction before concrete freeze. Inspected installed Mathlib
SetTheory/Ordinal/Notation.lean addAux/add/sub (lines 364–399), add_nf/repr_add
and sub_nf/repr_sub, and existing raw comparison decode-correct theorem.
These really are ordinary ordinal operations, not arithmetic formula syntax.

Addition must inspect the recursively obtained tail-plus-right result, not the
original right operand: addAux compares its exponent and combines coefficients
or drops/retains exactly in that result. Subtraction compares original heads,
returns the whole left notation on greater exponent, zero on smaller exponent,
and recurses through BOTH tails only on exactly equal positive coefficients.
Positive coefficient minus-one encoding must be calibrated in every branch;
natural truncated subtraction alone must not erase the unequal-coefficient
zero distinction. Raw comparison decode correctness is available for all codes,
so syntactic calibration need not assume normality.

For table lookup, prove every recursive paired index strictly below the current
index and table length exactly the current index before using lookup; malformed
non-normal codes still require total literal syntactic equality. Both-tail
subtraction decrease follows component monotonicity plus a strict tail decrease,
not an assumed ordering of arbitrary paired numbers. No output magnitude bound
is required by finite table primitive recursion, but intermediate output
construction and lookup must themselves have actual PR proofs.

Freeze separate all-input joint PR, all-code literal operation equality, and
normal-input NF/ordinary ordinal repr clauses. Any normalized-code constructor
used later must be an actual computed output with these calibrations, not a
choice of semantic representative. This supporting packet does not settle
full inverse threshold, translations, offset collisions or source arithmetic.
No compiler or edits to mathematical sources in this review.
