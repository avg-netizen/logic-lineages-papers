# Paper 17: exact initial removal of genuine short counts from the original live row

Printed source: `arithmetic.tex`, `thm:arithmetic`, entering high signed
normalization only after removing actual finite-gap count fields.

- Reuse #908 exact cleanup on the original live read list itself, not only the
  assembled output of a zero-class rewrite. Reuse #1210 literal syntax
  calibration, preserving the complete original order and signed weights.
- Each removed positive short count contributes exactly its signed original
  known interval length to the constant. Bare values and ordinary fields
  survive unchanged. Remaining count terms have genuine long shape;
  ranks and operands remain original. A malformed identity/interval count
  cannot become an accepted short contribution (the original read is owed).
- The original and cleaned value are the same at the given raw assignment;
  signed truth is exact at either polarity. Reverse truth needs existence
  of the genuine original input reads, and uses determinacy of literal
  ordered reader hits to compare the cleaned witness with the actual residue.
- This is not automatic payment of proper read tails across all inputs.
  The same statement can be applied at each replay whose original source
  reads are paid by #1231. A future all-large driver must still include
  original pre-cleanup read eligibility and cleaned-row replay thresholds.
