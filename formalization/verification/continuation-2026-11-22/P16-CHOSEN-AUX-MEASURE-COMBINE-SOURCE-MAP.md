# Paper 16: exact chosen auxiliary measure combine

Status: independent source-only candidate; exact proof and axiom gates
pending. No existing programs or paper claims are changed. Further design:
[P16-MEASURABLE-COMBINE-STAGE-TRANSPORT-DESIGN.md](P16-MEASURABLE-COMBINE-STAGE-TRANSPORT-DESIGN.md).

- The literal `chosenCombine` reads the original two child measure codes
  through actual unpair, computes the successor of the sum of child first
  coordinates, and selects the largest child second coordinate by the
  original less-than branch (keep the first on ties). It emits the actual
  unshifted standard pair, without a cons offset or Option tag.
- `exact_ChosenAuxMeasureCombine` proves original `CombineCalibrated`
  for this exact arity-two AST at every natural input. The pinned product
  and Nat decoders give `some n.unpair` on all inputs; there is no required
  canonical/reachable predicate and zero is the valid pair (0,0).
- `exact_OpenChosenAuxMeasureCombine` starts with both actual child pair
  graphs and the actual graph of this chosen combine. It produces one
  object existential numeral-bound witness shared by the actual output
  pairing and both weak numeral order formulas. The two weak depth
  formulas bound children by the exact predecessor of parent depth.
  Actual order cases supply the max branch; graph composition, child
  unpair/canonical inverse and literal addition/successor recover the
  real paired output. Nothing is reflected from the numeric proof.
- This does not establish reports for an arbitrary extensional P or
  from arbitrary unexplained child code reports. It does not install
  a new selected M, transport an actual grammar membership, or assert
  an unconditional own-cover theorem. The open proof does not import
  the numeric target or proof.

| Module suffix | SHA-256 |
| --- | --- |
| `NumberedWindowInternalChosenAuxMeasureCombineDefinitions` | `c70150d17cd39fafb151c71e0f6f0fddf90d8a4af392e32ab33a43c98eac08c1` |
| `NumberedWindowInternalChosenAuxMeasureCombineNumericTargets` | `44550e448881496e50f948ca736a834b4319becec81076596d7bddc3b4fe863d` |
| `NumberedWindowInternalChosenAuxMeasureCombineNumericProof` | `25192a6530336b734965007425d30aacbc242d6b57a85c020ee88364a37c074f` |
| `NumberedWindowInternalChosenAuxMeasureCombineOpenTargets` | `1f72362fb425c4b79e7b07082dfe0b2ab3d95d78d2f9ba109a70b9eaae4111d8` |
| `NumberedWindowInternalChosenAuxMeasureCombinePairProof` | `44db88e209b1bff23c35a286fdd61d7181e1072fc6a454562541d88aaf48e9e3` |
| `NumberedWindowInternalChosenAuxMeasureCombineOpenProof` | `a31cc5d198575878ab65255291296eb77330ca3386f5172b81e5502c862be14a` |
