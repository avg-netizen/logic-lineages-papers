# Paper 17: effective LongField comparison tails

**Target-only supplier.** No proof, native evidence, or numbered credit. The
reviewed existing `FullFieldComparison` is not modified.

Paper source: `17-permitted-control-canonical-comparison/sections/arithmetic.tex`,
ordinary fields, `lem:field-comparison`, and the requirement that a common
tail is chosen effectively after symbolic normalization (before finite-strip
handling). This packet covers the previously restricted LongField result
at **specified** computable tails, not yet arbitrary proper fields.

- `longFieldDistinctBound`: the witnesses in the four `distinct_*` case
  proofs in `FieldComparisonProof.lean`. Iterates-only is zero; mixed
  cases use the appropriate peel bound(s); entry/entry retains both peel
  bounds, the inverse-table tail for the same orientation, and
  `gapInputTail` with the Q interval listed first, exactly as in the
  existing proof. No smaller bound is claimed.
- `longFieldSameBound`: the same-input witnesses in the actual case
  proofs. Iterates-only zero; mixed peel the entry at other exponent plus
  one; entry/entry retains both peel bounds, both oriented gap tails, and
  the selected equal-gap certificate tail. No noncomputable witness
  selection or oracle.
- `LongFieldTailEffective`: literal numeric constructors and all-code
  primitive recursion for the omega-monomial, peel, and two comparison
  tail programs; exact calibration on source field encodings. Raw endpoint
  arithmetic, norms, certificates and gap bounds are the actual existing
  algorithms. Calibration covers even the syntax of non-LongField inputs;
  correctness is asserted only for LongFields. No claim about a raw
  normalizer for the *output form* in this stage.
- `LongFieldDistinctAtBound` and `LongFieldSameAtBound`: both selected
  controls; actual values at the prescribed shared or strictly ordered raw
  coordinates. Exact existing fixed answer/table form, including strict
  order and collisions. Actual comparison obligations are not handwaved
  from existential theorems: append proof adaptations retaining their
  witness expressions and exposing named bound hypotheses.

Next suppliers remain separate: raw form compiler/calibration, assembly
with the accepted short preprocessing on all three high-coordinate order
branches, true low-coordinate hit/miss evaluator and infinite-strip
substitution, and the concrete count replacement/termination bridge.
