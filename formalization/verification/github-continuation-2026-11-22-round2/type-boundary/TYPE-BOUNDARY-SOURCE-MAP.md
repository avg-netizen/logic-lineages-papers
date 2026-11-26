# Actual type codes and the finite refitted-checker boundary

Reviewed source head: `b28541e6f1682fc41c47a385729df36e9db87b0d`.

Supporting continuation of #1453, #1461 and #1464. No numbered Paper 16 statement is promoted. The target propositions are frozen before proof authoring; their hashes are recorded in `LEDGER.md`.

## Source/statement findings

The three accepted packets state their conditional results correctly. #1453 replaces the two type-guard derivations by `TypeGuardArrowCalibration`; its sufficient component `SyntaxGuardRefits` is not supplied. #1461 changes the scalar type checker to `refittedScalarType s TV T = conjunction TV (refitGuard s T)` and retains two internal codomain-inversion premises. It does not discharge those premises for the actual source carrier. #1464 correctly distinguishes the all-valid-type condition `AllTypesWindowed s` from `AcceptedTypesWindowed s`, which concerns only types of addresses accepted by the original scalar.

The remaining finite-list obstruction is stronger than #1464's conditional implication. `refitGuard s T` includes the actual program `grammarTypeAt s`, which tests membership in the finite literal list `s.types`. Therefore the refitted checker rejects a valid type outside that list for every choice of `TV` and `T`. No calibration of `T`, grammar inclusion, or source soundness assumption is needed for that numerical conclusion.

A documentation boundary in round 4 merits preserving: `HANDOFF.md` describes the tuple obstruction using the types of accepted addresses. The exact tuple condition is `ActualTypeGuard`, which quantifies over **all** valid type codes; `AcceptedTypesWindowed` instead governs the separate extensional scalar-calibration equivalence. The new targets keep these questions distinct.

## Original definitions used

Paths below are relative to `formalization/`.

- `LogicLineages/PersistentMarking/NumberedWindowAddressAlgorithm.lean`: `nextType`, `typeTable`, and `typeBit` are the original numeric type-recognition algorithm. The arrow branch reads both earlier decoded components.
- `LogicLineages/PersistentMarking/NumberedWindowAnnotationAlgorithm.lean`: `arrow dom cod = NumberedWindowPairAlgorithm.pair dom cod + 1` is the original arrow-code constructor.
- `LogicLineages/PersistentMarking/NumberedWindowInternalSparseFieldParserRawPairProof.lean`: accepted `encodedPair` and `tailBound` concern the same original polynomial pairing and its decoder.
- `LogicLineages/PersistentMarking/NumberedWindowInternalSettingsGrammarGuardDefinitions.lean`: `grammarTypeAt s` calls the original scratch-membership program on `Encodable.encode s.types`; `refitGuard s T` is its conjunction with the supplied `T`.
- `LogicLineages/PersistentMarking/NumberedWindowInternalCoverMeasuredApplicationTypeCalibrationTargets.lean`: the refitted checker is the literal conjunction of `TV` and `refitGuard s T` used in #1461.
- `LogicLineages/PersistentMarking/NumberedWindowInternalCoverMeasuredApplicationRefittedInstallTargets.lean`: `AllTypesWindowed s` requires every `typeBit`-valid code to belong to `s.window.1`. `AcceptedTypesWindowed s` is a distinct predicate.
- `LogicLineages/PersistentMarking/NumberedWindowInternalSparseAddressPositiveCalibrationTargets.lean`: `ActualTypeGuard` is equality with the original `typeBit` on every natural input.
- `LogicLineages/PersistentMarking/NumberedWindowInternalSparseTupleDefinitions.lean`: `InstalledTupleAt` includes `CallbacksAt`, whose literal second conjunct is `ActualTypeGuard` of the installed type-checker slot.

The numerical membership proof uses the existing all-input scratch-membership calibration, the original literal-program evaluation, and the existing list-code round trip. The valid-code construction works directly against the original `typeTable`; it does not substitute a new type recognizer or require importing the legacy arithmetic-code family or its module-system copies.

## Frozen targets

Module: `LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredApplicationTypeBoundaryTargets`.

| Target | Exact scope |
| --- | --- |
| `ExactTypeBitArrowLaw` | `typeBit (arrow dom cod) = typeBit dom && typeBit cod`, for all numeric components. |
| `ExactValidArrowCodeChain` | The explicit recursion `arrowCodeChain 0 = 0`, `arrowCodeChain (n+1) = arrow 0 (arrowCodeChain n)` produces a valid code at least `n`. |
| `ExactValidTypeCodesUnbounded` | A valid code exists above each numeric bound. |
| `ExactFiniteTypeListOmission` | Every finite list of natural codes omits a valid code. |
| `ExactNoAllTypesWindowed` | `AllTypesWindowed s` is false for every `Settings` value. |
| `ExactRefittedValidTypeRejection` | For arbitrary `s`, `TV`, and `T`, one valid code has numeric output zero under `grammarTypeAt s`, `refitGuard s T`, and the refitted scalar type checker. |
| `ExactActualTypeRefitCounterexample` | If `TV` has the actual all-code calibration, a literal arrow with domain zero and some valid codomain is accepted by `TV`, as are its two components, while the refit guard rejects the codomain. |
| `ExactRefittedTypeGuardNeverActual` | No refitted checker satisfies `ActualTypeGuard`, without any component calibration premise. |
| `ExactRefittedInstalledTupleImpossible` | No `InstalledTupleAt` has the refitted checker in its type-checker slot, without any component calibration premise. |

The code chain concerns natural syntax codes only. It is unrelated to the ordinal-tower work elsewhere in the continuation.

## What is assumed

Only `ExactActualTypeRefitCounterexample` assumes `ActualTypeGuard TV`, because its conclusion explicitly describes the supplied program's acceptance. The other targets have no mathematical premises beyond their ordinary parameters. In particular, the two impossibility targets do not assume `TypeGuardCalibrated s T`, `GrammarTypeInclusion s`, or `ActualTypeGuard TV`.

## What is not claimed

- No internal `ArrowCodomainInversion`, `SyntaxGuardRefits`, or `TypeGuardArrowCalibration` is proved or refuted for arbitrary object-calculus bodies. The arrow law and counterexample are numerical facts. No numeric calibration is reflected into the object calculus.
- No application guards are discharged. The original carrier, window, least, scalar and application definitions remain unchanged.
- The impossibility of full `ActualTypeGuard` does not refute `AcceptedTypesWindowed s`, nor does it establish that the refitted scalar differs extensionally from the original scalar for every setting. #1464's separate conditional equivalence remains applicable.
- No `GuardedAt`, source interpretation, or numbered Paper 16 theorem is closed. The result blocks this finite-checker substitution as a way to obtain an accepted installed tuple.
- Existing accepted files, frozen source maps, source hashes and native evidence remain unchanged. Proof validity is to be established by the root's single exact native/axiom gate, not by a duplicate manual acceptance review.

## Status at target freeze

Targets and this map are written. No proof module exists at freeze time. Native compilation is pending and belongs to the root's sole queue. Failed proof drafts will be retained before any repair.
