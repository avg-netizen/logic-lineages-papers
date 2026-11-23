# Refitted installation guards — source map (Fable-2, round 4, G06)

Modules: `LogicLineages/PersistentMarking/NumberedWindowInternalCoverMeasuredApplicationRefittedInstall{Targets,Proof}.lean`.
Receipt `1795404207507881578-3290394`. Every theorem: `[propext, Classical.choice, Quot.sound]`.

Subject: the scalar type checker of #1461, `refittedScalarType s TV T = conjunction TV (refitGuard s T)`,
against the accepted installation's numeric calibration `ActualTypeGuard tv : ∀ n, evaluate tv [n] =
(typeBit n).toNat`.

## Claimed (gated)

All statements are about natural-number evaluation of programs. None is a rule of the object calculus.

| Theorem | Statement |
|---|---|
| `exact_RefittedScalarTypeCalibrated` | `GrammarTypeInclusion s`, `ActualTypeGuard TV`, `TypeGuardCalibrated s T` ⟹ the refitted checker computes `typeGuard s` (= `typeBit n && s.window.1.contains n`) on every input. |
| `exact_RefittedTypeGuardActualOnlyIf` | `TypeGuardCalibrated s T` and `ActualTypeGuard (refitted)` ⟹ `AllTypesWindowed s`. |
| `exact_RefittedTypeGuardActualIff` | Under the three calibrations above: `ActualTypeGuard (refitted) ⟺ AllTypesWindowed s`. |
| `exact_RefittedInstalledTupleOnlyIf` | `TypeGuardCalibrated s T` and `InstalledTupleAt xs s W i j cv (refitted) d p₀ raw least v` ⟹ `AllTypesWindowed s`, for all other arguments. |
| `exact_RefittedAddressScalarCalibrationIff` | Under `GrammarTypeInclusion s`, `ActualContextGuard cv`, `ActualTypeGuard TV`, `TypeGuardCalibrated s T`, `ActualPackedWindow s W`, `ActualLeastCalibration s least`: `ActualScalarCalibration s (addressScalar cv (refitted) W least) ⟺ AcceptedTypesWindowed s`. |
| `exact_RefittedInstalledScalarCalibrationIff` | The same equivalence for `Q.scalar`, `Q := install s V TV M M0 B T base cv (refitted) root other`, with `ActualPackedWindow s Q.window` and `ActualLeastCalibration s Q.least` as hypotheses. |

Named conditions (both `def … : Prop` in the targets module):

- `AllTypesWindowed s := ∀ n, typeBit n = true → s.window.1.contains n = true`.
- `AcceptedTypesWindowed s := ∀ q ctx ty k, addressView q = some (ctx, ty, k) → canonical s (ctx, ty, k) =
  true → s.window.1.contains ty = true`.

Suppliers: `NumberedWindowInternalSparseCanonicalAddressNumericProof.calibration`
(`ExactAddressScalarCalibration`), `exact_SettingsRefitGuardCalibration`, `acceptedBoth`,
`conjunctionEvaluation`, `decodedOf`, `decodedView`, `viewDecoded`, `fields`, `applyValue`. The six-line
private lemma `shapeOne` restates the private `shape` of `…SparseCanonicalAddressNumericProof.lean`
with the same proof text.

## Assumed (hypotheses, not discharged here)

- `GrammarTypeInclusion s` (window types are grammar types). The accepted statements that use
  `refitGuard` carry the same premise.
- `ActualTypeGuard TV`, `TypeGuardCalibrated s T`, `ActualContextGuard cv`: the accepted calibrations of
  the component programs.
- `ActualPackedWindow s W`, `ActualLeastCalibration s least`. For the measured route these are stated
  on `Q.window` and `Q.least`; it was **not checked** whether an accepted theorem supplies them for
  `thinMatchingWindow` and the measured `packedLeastProgram`. `GuardedAt` supplies the corresponding
  facts for its own factored route, which is a different window and exchange.
- `AcceptedTypesWindowed s` itself, wherever the equivalence is used left to right. It is a condition
  on the settings; it is not derived from anything.

## Not claimed

- That `AllTypesWindowed s` is false. It is false for every `s` by this argument, which is **not
  gated**: `typeBit 0 = true` and `typeBit` is closed under pairing of valid codes
  (`NumberedWindowAddressAlgorithm.nextType`; equivalently `exact_ExactTypeGuard : typeBit n =
  (decodeTy n).isSome`), so valid codes are unbounded, while `s.window.1` is a finite list. Granting
  it, `exact_RefittedInstalledTupleOnlyIf` reads: `InstalledTupleAt` never holds at the refitted
  checker, hence no witness of `GuardedAt` or `ConcreteAddressPositive` has it as `tv`.
- That `AcceptedTypesWindowed s` holds for the settings of the paper, or that it reduces to a finite
  check over the window. The round-3 reading that `termParts` tests no type for tag-4 keys suggests it
  can fail; that reading is not gated either.
- Any statement about `ActualAddressPositiveCalibration` at the refitted checker (the `positive`
  program `addressPositive cv tv raw least`), about `TupleAt`'s `Evaluates`/`Interprets` components, or
  about `EdgeCarriersAt`. `AddressPositiveComposition` uses `ActualTypeGuard tv` in both directions in
  the same way as the scalar calibration, so the same kind of condition is expected; not proved.
- Anything about the two open codomain-inversion premises of #1461.
- Any derivation in the object calculus. The derivation-level installation facts (#1430's four
  statements; the general application statements of #1438/#1440/#1442) are quantified over every `tv`
  with no calibration hypothesis; they apply to the refitted checker by instantiation, which is what
  #1461 already does. Nothing new is gated about them here.

## Reading of #1461

- Its statements are true as stated and unaffected: they are derivation-level statements about
  `install … (refittedScalarType s TV T) …` and use no numeric calibration of the type checker.
- The scalar in them is **not** the scalar of an accepted `InstalledTupleAt` / `GuardedAt` tuple: that
  predicate requires `ActualTypeGuard tv`, which the refitted checker has only if every valid type
  code is windowed. So #1461 cannot be composed with any statement that takes `InstalledTupleAt`,
  `CallbacksAt` or `GuardedAt`'s tuple as given.
- Whether its scalar is at least extensionally the original scalar algorithm is now exact:
  it is, on every input, if and only if `AcceptedTypesWindowed s` (given the listed calibrations).
  Without that condition the refitted route accepts strictly fewer addresses than `scalar s`.
