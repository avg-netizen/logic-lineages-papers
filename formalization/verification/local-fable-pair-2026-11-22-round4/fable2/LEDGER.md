# Fable-2 ledger — local round 4 (2026-11-22)

## G06 — refitted installation guards

### Plan

Task: settle the caveat of #1461 (round 3, G05): does the accepted installation survive when the
scalar's type checker is `refittedScalarType s TV T = conjunction TV (refitGuard s T)` instead of a
program calibrated to `typeBit`?

What was read: round-3 ledger section G05 and `1461-SCOPE.txt`; the two `…TypeCalibration…` modules;
`NumberedWindowInternalSparseAddressPositiveCalibrationTargets.lean`,
`…SparseTupleDefinitions.lean`, `…SparseCanonicalAddressTargets.lean`,
`…SparseAddressPositiveNumericSideProof.lean`, `…SparseAddressPositiveNumericCompositionProof.lean`,
`…SparseCanonicalAddressNumericProof.lean`, `…SettingsGrammarGuardNumericProof.lean`,
`…CoverCombinedMeasuredInstall{Definitions,Targets}.lean`, `NumberedWindowScalarAlgorithm.lean`,
`NumberedWindowAddressAlgorithm.lean`, `GuardedAt` in `…GuardedMatchingInstallationTargets.lean`
(lines 91–116), the #1430 entry of `verification/github-continuation-2026-11-22/root/ACCEPTANCE.json`;
greps for definitions and lemma names.

Where `ActualTypeGuard tv` occurs (complete grep over `LogicLineages/`: 12 hits in 5 files):

| Site | Role of `ActualTypeGuard tv` | What it is used for |
|---|---|---|
| `AddressPositiveComposition` (`…AddressPositiveCalibrationTargets.lean:33`) | hypothesis | `reportsOf` (type field of a decoded address passes `tv`) and `decodedOf` (a passing `tv` gives `typeBit`); both directions, so `addressPositive cv tv raw least` computes the original `positive` on every input |
| `ConcreteAddressPositive` (same file, `:43`) | conjunct under `∃ tv` | the chosen `tv` is produced with this calibration |
| `ExactAddressScalarCalibration` (`…CanonicalAddressTargets.lean:43`) | hypothesis | same two lemmas; `addressScalar cv tv W least` computes the original `scalar s` on every input |
| `CallbacksAt` (`…SparseTupleDefinitions.lean:33`) | conjunct | part of `InstalledTupleAt` (three instances inside `GuardedAt`, each with the existential `tv`) |
| `…NumericSideProof.lean`, `…NumericCompositionProof.lean` | hypothesis of the lemmas above | — |

Where it does not occur: the four statements of #1430
(`ExactInstalledCarrierCoordinates`, `ExactInstalledCarrierFromCoordinates`,
`ExactInstalledApplicationReport`, `ExactInstalledMeasurePreserving`) quantify over every `cv tv` with
no calibration hypothesis, and so do the general application statements of #1438/#1440/#1442 that
#1461 instantiates. `TypeGuardCalibrated s T` concerns the window's guard `T` (a different slot);
in `GuardedAt` it is a conjunct on the existential `T`, independent of `tv`.

Diagnosis before any target was written:

1. The derivation-level facts #1461 relies on (`exact_InstalledCarrierCoordinates` and the three
   general application theorems) hold for every `tv`, the refitted one included. Nothing to repair.
2. The numeric chain does not accept the refitted `tv` as stated. Under the accepted calibrations
   (`ActualTypeGuard TV`, `TypeGuardCalibrated s T`, `GrammarTypeInclusion s`) the refitted checker
   computes `typeGuard s n = typeBit n && s.window.1.contains n`, so `ActualTypeGuard` of it says
   "every valid type code is in the finite window list". `CallbacksAt`, hence `InstalledTupleAt`, at
   the refitted `tv` carries that conjunct literally. So no `GuardedAt` witness has the refitted `tv`.
3. The conclusion the scalar's calibration lemma delivers (`ActualScalarCalibration s (addressScalar
   cv tv W least)`) does not need `ActualTypeGuard tv` itself: it needs only that the narrower checker
   never rejects the own type of an address the original scalar accepts. That is a numeric condition
   on `s`, and it is also necessary.

Targets: (i) refitted checker is `TypeGuardCalibrated s`; (ii) `ActualTypeGuard` of it ⟹ / ⟺
`AllTypesWindowed s`; (iii) `InstalledTupleAt` at it ⟹ `AllTypesWindowed s`; (iv) scalar calibration of
`addressScalar cv (refitted) W least` ⟺ `AcceptedTypesWindowed s`, and the same for
`(install … (refitted) …).scalar` given calibration of that route's window and least programs.

Not attempted: falsity of `AllTypesWindowed s` for every `s` as a gated theorem (it needs unboundedness
of valid type codes; `exact_ExactTypeGuard : typeBit n = (decodeTy n).isSome` exists but the
encode/decode round trip was not read). The analogous equivalence for
`ActualAddressPositiveCalibration` (the `positive` checker) and for `TupleAt`'s `Evaluates` component.
The two codomain-inversion premises of #1461 (excluded by the brief).

### Targets + sha256 (recorded before the proof module was drafted)

`LogicLineages/PersistentMarking/NumberedWindowInternalCoverMeasuredApplicationRefittedInstallTargets.lean`
sha256 `2f7a939c10318ad42e109b4a52a7b7cebab8618a476b2b9e75b9a308577c2ba1`

Definitions: `AllTypesWindowed s := ∀ n, typeBit n = true → s.window.1.contains n = true`;
`AcceptedTypesWindowed s := ∀ q ctx ty k, addressView q = some (ctx, ty, k) → canonical s (ctx, ty, k) =
true → s.window.1.contains ty = true`.
Statements: `ExactRefittedScalarTypeCalibrated`, `ExactRefittedTypeGuardActualOnlyIf`,
`ExactRefittedTypeGuardActualIff`, `ExactRefittedInstalledTupleOnlyIf`,
`ExactRefittedAddressScalarCalibrationIff`, `ExactRefittedInstalledScalarCalibrationIff`.

### Receipts

- `1795404007563949015-3288977` (`build-reports/1795404007563949015-3288977.json`, sha256
  `d1f7f8582ecb748b99605c8dcda2c68debd570aeb635254e50b17c12e5cefb13`) — `gate.sh mathlib` on
  `…RefittedInstallTargets` alone, before the proof module was drafted: COMPILE_PASS.
- `1795404207507881578-3290394` (`build-reports/1795404207507881578-3290394.json`, sha256
  `da59a0706320f087a990af21fa01c4b7fd8865ce2ca7308875420f1c98275872`) — `gate.sh mathlib` on
  `…RefittedInstallTargets` and `…RefittedInstallProof`: COMPILE_PASS for both. Six `#print axioms`
  lines, each `[propext, Classical.choice, Quot.sound]`.
- Proof module sha256 `f541417b219f45cdd85bea8b6601e8e4dafd8265436fa9cd7b4dbd05c61ed0bc`; targets
  sha256 unchanged from the frozen value above.

### Failures

No failed gate (two runs, both passed). One shell command was refused by the permission mode (a
Python heredoc used only to reformat grep output); the grep was rerun with the search tool instead —
no effect on the work.

Not achieved, stated as limits of the result rather than of the compiler:
- `AllTypesWindowed s` is not refuted by a gated theorem. The refutation is an argument (valid type
  codes are unbounded, the window list is finite), recorded as such in the source map.
- `AcceptedTypesWindowed s` is a hypothesis on the settings. Nothing shows it holds for the paper's
  settings or reduces to a finite check.
- Calibration of the measured route's own `Q.window` / `Q.least` is a hypothesis of the install-level
  statement; no accepted supplier was looked for.
- `ActualAddressPositiveCalibration` and `TupleAt` at the refitted checker were not examined.

### State and next

STOPPED AT FIRST GATED STATEMENT. The caveat of #1461 is settled as follows.

- Gated: under the accepted calibrations the refitted checker computes `typeGuard s`;
  `ActualTypeGuard` of it ⟺ `AllTypesWindowed s`; `InstalledTupleAt` at it ⟹ `AllTypesWindowed s`;
  the refitted address scalar (general, and the measured route's `Q.scalar`) is calibrated to the
  original `scalar s` ⟺ `AcceptedTypesWindowed s`.
- By reading, not gated: #1430's four statements and the application statements #1461 instantiates
  carry no `ActualTypeGuard` hypothesis, so #1461's own statements stand.
- Consequence: #1461 is about a route whose type checker is not the `tv` of any accepted
  `InstalledTupleAt` (granting the unboundedness argument), and whose scalar equals the accepted
  scalar algorithm exactly when `AcceptedTypesWindowed s`.

Evidence in `REFITTED-INSTALL-EVIDENCE.json`; claims and non-claims in
`REFITTED-INSTALL-SOURCE-MAP.md`.

Next, in order:
1. Decide `AcceptedTypesWindowed s` for the actual settings: either prove it from `ValidWindow s W` /
   `TypeSupport s W` (a numeric lemma "a `canonical` address has a windowed own type", by shape of the
   key — the round-3 reading of `termParts` says tag 4 is the case to look at), or exhibit a settings
   value where it fails. If it fails, the refitted route is strictly narrower than the accepted scalar
   and #1461 should be kept as a side result only.
2. If it holds: restate the tuple layer with a relaxed callback (`TypeGuardCalibrated s tv` in place of
   `ActualTypeGuard tv`) and redo `AddressPositiveComposition` under the analogous condition on
   `positive`-accepted endpoints; check which consumers of `CallbacksAt` use the `ActualTypeGuard`
   conjunct at all.
3. Find or prove `ActualPackedWindow s Q.window` and `ActualLeastCalibration s Q.least` for the
   measured `install` route; without them the install-level equivalence has undischarged hypotheses.
4. Optional, cheap once the `decodeTy`/`encodeTy` round trip is read: gate `¬ AllTypesWindowed s`.
