# One actual affine → fixed-head graph guard as ordered rows

Paper 17, `17-permitted-control-canonical-comparison/sections/arithmetic.tex`, lines 1–53 (flattening, natural affine gate and proper fixed-head collapse equation) and 225–274 (why a true graph must be retained in later low-strip polarity work).

- Row 1 keeps every signed affine occurrence and uses the original natural value at the input name. Its zero test is exactly the source affine graph at the given valuation, even when ranks repeat; it assumes no fresh-variable extension or independent assignments.
- Row 2 explicitly records the **ordinal norm** affordability inequality at the original input, not an asymptotic solver cutoff. The original guard and successful collapse read already imply this inequality.
- Row 3 reads the real ordinary entry value at iterate 0 and the exact proper count, in that order, from the **same** raw proper-entry result at the literal zero target. The output occurrence is the original natural output name. Invalid and genuine miss cannot produce an ordered row value.
- The theorem identifies the exact three ordered numeric entries and truth bits of a passing snapshot at one shared valuation. It does not lower arbitrary DAGs, construct an extension, establish low slices for circuit guards, or compile symbolic decisions. An eventual consumer must conjoin this guard outside either polarity of the original test.

`AffineCollapseGuardRowsTargets` contains the definition and exact proposition.
`AffineCollapseGuardRowsReadProof` calibrates genuine coordinate, value and count occurrences.
`AffineCollapseGuardRowsProof` uses the existing original affine and fixed-head guard semantics; `AffineCollapseGuardRowsStatementChecks` exports the exact alias.
No Lean/native gate was run by the author.
