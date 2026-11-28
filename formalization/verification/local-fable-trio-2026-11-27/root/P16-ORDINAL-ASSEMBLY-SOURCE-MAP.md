# Paper 16 ordinal assembly — source map (root lane, 27 November 2026)

Serves `verification/paper16-remaining-targets-2026-11-25/TARGETS.md`, section "Ordinal inputs and
assembly", items 1 and 4, and the `thm:upper`, `lem:tower-cofinality`, `thm:height`, `thm:main` rows of
its table.

Targets module: `LogicLineages.NativeModule.PersistentMarking.Paper16OrdinalAssemblyTargets`.
Proof module: `…Paper16OrdinalAssemblyProof`.

## What is proved outright (existing targets of `Paper16RemainingOrdinalTargets`)

- `OrdinalSemanticsExistence` — a solution of the arithmetic and omega equations exists
  (from `ActualCollapseMain.solutionExists`). TARGETS.md item 1.
- `CofinalityAtActualEndpoint` — first equality of `lem:tower-cofinality` on the actual collapse, for
  every solution (from `actualTowerCofinality`).

## What is proved as an implication (new targets, frozen before proof)

| Target | Says |
| --- | --- |
| `EndpointSelfIdentification` | `ψ(Λ)` of a collapse identifies its own endpoint (definitional). |
| `CalibrationFromPointwise` | `AllTowerCalibration → CalibrationForAssembly`. |
| `UpperFromInputs` | `NormAtActualEndpoint → UniformAccessibility → UpperAtActualEndpoint`. |
| `UpperAtCitedFromAccessibility` | `UniformAccessibility → UpperAtCitedOrdinal citedBH` for every ordinal. |
| `CitedCofinalityFromIdentification` | `IdentifyCitedEndpoint citedBH → CofinalityAtCitedOrdinal citedBH`. |
| `HeightFromInputs` | norm at endpoint, accessibility, pointwise calibration ⟹ `HeightAtActualEndpoint`. |
| `PrincipalFromInputs` | the same three ⟹ `PrincipalAtActualEndpoint`. |
| `PrintedFromInputs` | at an independently given `citedBH`: norm theorem there, accessibility, pointwise calibration, endpoint identification ⟹ upper statement, tower supremum `= citedBH`, effective height, coded-effective main statement. |

## What is not claimed

None of the four inputs is discharged: the inductive-norm theorem (Pohlers), `UniformAccessibility`
(`lem:arithmetic-accessibility`), `AllTowerCalibration` (Simmons; proved only for n = 0, 1, 2) and the
identification of the endpoint with the cited ordinal. No numbered statement becomes checked by this
module: the register rule excludes added premises. The use is bookkeeping — after it, each of the four
pending ordinal statements is exactly "these named inputs", stated against the fixed targets of 25
November rather than against per-solution quantifier prefixes.
