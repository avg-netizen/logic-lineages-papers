# One actual arbitrary fixed head on the original shared source/output wires

Paper 17, `17-permitted-control-canonical-comparison/sections/arithmetic.tex`, lines 3–27 and 33–48.

- A canonical finite head is exactly the actual natural affine gate with constant the original finite head value and one occurrence of the original source wire. No intermediate variable is needed.
- An infinite canonical head uses the actual raw normal split. Its one fresh hidden wire is the exact norm input (N(\lambda)+(k+u)), using the norm and finite remainder of the original head and the **same** existing source wire. The proper limit-collapse graph uses the **same** existing output wire. The original raw gate holds iff the new graph holds with that unique transported value, and no other wire is changed. Inconsistent outputs cannot be repaired by the hidden wire.
- The typed calibration supplies the decoded canonical limit head, actual domain and original ordinal initial state, not a guessed shift or asymptotic bound. Interpretation as the original ordinal collapse is explicit under the existing selected-control hypothesis. Raw circuit-reader equivalence itself does not assume that hypothesis.
- This is a semantic one-gate normalization, not a mixed circuit elaborator, ordering algorithm, new compiler/decoder effectivity, global low-stratum extension, or symbolic decision theorem.
