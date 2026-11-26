# Paper 17 supplied-policy lane — 22 November 2026

- Scope assessment completed in `CORRESPONDENCE-REVIEW.md`: the current
  main comparator does not expose uniformity in a supplied policy program.
  No material mismatch found for the standalone arithmetic and fixed-policy
  ground comparators. No register entry changed.
- Root assigned the bounded first macro-interpreter bridge, with no local
  compiler or Git execution by this lane.
- **FROZEN, before proof authoring:**
  `LogicLineages/PermittedControl/PolicySuppliedCodeMacroTargets.lean`,
  SHA-256 `e551e5e34aee4a8ea9bbddcf8a8d1e4a1080fddfd2c4fb321a242000ccb9c580`.
  Exact targets: `MacroPartrec`, `ExactMacroCalibration`, their conjunction
  `FullSuppliedCodeMacro`. Definitions retain the existing selector and raw
  macro expansion, with `Part (Option Nat)` distinguishing divergence and
  syntactic rejection.
- Source scope frozen in `POLICY-SUPPLIED-CODE-MACRO-SOURCE-MAP.md`, SHA-256
  `1bc117778308723c0d55e74774f2243d62c3dfe497448863fa2ae62ce6be0fc6`.
- A lexical conflict was caught before proof authoring or compilation:
  `macro` is a Lean command keyword. The original frozen file is preserved
  byte-for-byte as `drafts/PolicySuppliedCodeMacroTargets.v1.keyword.lean.txt`.
  A new module, `PolicySuppliedCodeMacroInterpreterTargets.lean`, uses the
  declaration name `macroEval`. The source-map discussion of `macro`
  refers to that same interpreter; no proposition or domain was changed.
- **FROZEN replacement before proof authoring:**
  `LogicLineages/PermittedControl/PolicySuppliedCodeMacroInterpreterTargets.lean`,
  SHA-256 `9917d145471ea6dac23788ad560a864d18c072b09750edb64628ff815241ce97`.
- **READY for root's native queue:**
  `LogicLineages/PermittedControl/PolicySuppliedCodeMacroProof.lean`,
  SHA-256 `c33d8289003cfbb809cf67e629da49e2751fb4a3f3269f99f5235566e71e5466`.
  Exact exported theorems: `macroPartrec`, `exactMacroCalibration`,
  `fullSuppliedCodeMacro`. Standard axiom print commands are included.
  The target hash still matches its freeze; static forbidden-token scan
  found no `sorry`, `axiom`, `native_decide`, or `admit` declaration.
  This lane has not run a compiler; the draft is not yet a checked result.
- Root assigned one bounded extension: exact equivalence of the supplied
  code's realization relation and the existing `PolicyShape.Effective`
  policy class. The original interpreter target remains unchanged.
- **FROZEN before extension proof authoring:**
  `LogicLineages/PermittedControl/PolicySuppliedCodeRealizationTargets.lean`,
  SHA-256 `3c98dfe4874f3b819c80114139299866f93e6eacec52854eb49403e5571bfcbd`.
  Targets: `EffectiveHasCode`, `RealizedIsEffective`,
  `ExactPolicyCodeRealization`.
- Extension source map `POLICY-SUPPLIED-CODE-REALIZATION-SOURCE-MAP.md`,
  SHA-256 `f7a15581e2d7391077aef19f5c2b0543da2849e0b62ef578077cd06e0b281e18`.
- **READY for root's native queue:**
  `LogicLineages/PermittedControl/PolicySuppliedCodeRealizationProof.lean`,
  SHA-256 `137ef49df67a9d47f9dd33447e7b6e8af9893f7ff9e4a2accd3d7ae08146c7f6`.
  Exact endpoints `effectiveHasCode`, `realizedIsEffective`, and
  `exactPolicyCodeRealization` include axiom print commands. Both frozen
  target hashes still match; the new extension has no forbidden proof
  placeholders. No compiler was launched by this lane. This remains a
  drafted, ungated result until root supplies its native receipt.
- **NATIVE PASS, first attempt for both proof modules:** root's serialized
  receipt `build-reports/1795394451020498412-12.json` records return code 0
  for both frozen target modules and both proof modules. All four source
  hashes still match the frozen/ready hashes above. The receipt covers the
  3,712-module dependency closure; no duplicate replay was performed here.
- The six exact aliases `macroPartrec`, `exactMacroCalibration`,
  `fullSuppliedCodeMacro`, `effectiveHasCode`, `realizedIsEffective`, and
  `exactPolicyCodeRealization` report only `propext`, `Classical.choice`,
  and `Quot.sound`. Root is packaging supporting records **#1433** (macro)
  and **#1434** (realization), with evidence paths
  `evidence/1433-p17-supplied-code-macro-native.json` and
  `evidence/1434-p17-supplied-code-realization-native.json` relative to
  `verification/github-continuation-2026-11-22/`.
- Final scope check: the passed propositions retain precisely the stated
  single-macro interpreter and equivalence with the original effective
  policy class. Calibration gives termination on realizing selector
  programs, including syntactically rejected operand lists; it does not
  assert termination on arbitrary policy codes. No scope mismatch found.
  Uniform source compilation, uniform ground comparison, and the supplied
  near-control-parameter interface remain open; `thm:main` is not promoted.
  Only this ledger was edited for the pass hand-back. No compiler, Git,
  source-map, Lean-source, register, or pin change was made by this lane.
