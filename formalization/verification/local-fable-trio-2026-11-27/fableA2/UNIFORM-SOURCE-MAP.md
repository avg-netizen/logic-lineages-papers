# Source map — uniform type-level targets (Fable A2, 27 November 2026)

Frozen target modules (in `LogicLineages/NativeModule/PersistentMarking/`, namespace
`LogicLineages.PersistentMarking.ActualCalibrationUniform`); sha256 values are in `LEDGER.md` Entries 2 and 4.

| file | first gated in |
|---|---|
| `ActualCalibrationUniformTargets.lean` | `1795815470684857486-1099377` |
| `ActualCalibrationUniformWeightTargets.lean` | `1795816095108793665-1103069` |

## What they serve

Paper 16, `sections/ordinals.tex` 552–575 (`Δ_n = ψ_B(a_n)` "by the cited calibration"), i.e. the TARGETS.md
checkpoint `Paper16RemainingOrdinalTargets.AllTowerCalibration`, through root's per-level interface
(`ActualCalibrationLevelsTargets`: `LevelFactsAt l`, `PsiTowerLevelAt l`, `exact_AllFromLevels`). They are
intermediate layers, not paper statements; the paper cites Simmons 2004 §§5–6 / 2008 Thm 5.10 for the calibration.
Design and paper checks: `UNIFORM-INDUCTION-PLAN.md`.

## Assumed

Every solution-dependent statement quantifies over an arbitrary solution of `OrdinalArithmeticEquations` and
`OmegaArithmeticEquations` (as all earlier calibration targets do). `OrbitWeight` assumes
`NormSeparated σ' (σ+1)` and `Ω^(σ+1) ≤ Λ`. Weights are steps only under the chain condition `CondDown`.

## Not claimed

- No closed formula for ψ; a weight says nothing at an inactive index (`StepLow` needs activity) or outside
  `CondDown`.
- `TowerWeight` is "weight 0 at the object's own type"; nothing about weights other than those produced by
  application and orbits.
- `AllLevels` is exactly root's per-level hypothesis of `exact_AllFromLevels`; `AllTowerCalibration` itself is
  concluded in a separate module.
- The norm theorem, accessibility and the endpoint identification (the other inputs of the pending statements)
  are untouched.
