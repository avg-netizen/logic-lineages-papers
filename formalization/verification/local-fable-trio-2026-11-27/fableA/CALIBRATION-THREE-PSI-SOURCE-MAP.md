# Source map — `ActualCalibrationThreePsiTargets` (Fable A, 27 November 2026)

File: `LogicLineages/NativeModule/PersistentMarking/ActualCalibrationThreePsiTargets.lean`
sha256 `0817507591f2b257b06358724322eedc4b90bf57e2b67b3c01ad8cf001ed4c32`.

## What it serves

Paper 16, `sections/ordinals.tex` 552–575: "The resulting sequence (D) satisfies `Δ_n = ψ_B(a_n)` by the
cited calibration", instance `n = 3` (`Δ_3 = B_1 B_0 N_B Γ_0`, `a_3 = Ω^Ω`), with ψ_B the clause-(P)
collapse of 593–610 (`ActualCollapse.veblenData`). TARGETS.md checkpoint: `AllTowerCalibration`
(`Paper16RemainingOrdinalTargets`), instance 3. The statements are intermediate layers for the frozen
`ActualCalibrationThree.PsiPowerLevel` (T4) and `CalibrationThree` (T5); they are not paper statements.

## Definitions

- `levelEnum fix pow β α = orbit .base (level fix pow β) zeroValue α` — `E_β(α) = (D β)^α(0)`.
- `psiO fix pow w ξ` — the actual collapse as a total function on ordinals: `ψ ⟨ξ, _⟩` for `ξ ≤ Λ`, `0`
  otherwise. The value above `Λ` is junk and is never used (every lemma carries `ξ ≤ endpoint`).
- `NormSeparated ζ e` — `∀ τ < Ω^e, |ζ + τ| = max |ζ| |τ|`. An abstract stand-in for "ζ is a multiple of
  `Ω^e`"; only the norm consequence is ever needed.

## Statements and what is assumed

All are for every solution of the arithmetic and ω equations (same binder block as the neighbours).

| name | statement | proved in |
|---|---|---|
| `VeblenDoubling` | `y + y ≤ N_B y` | `…HierarchyProof.veblenDoubling` |
| `LevelStrict` | `D β x < D (β+1) x`; `L` strictly increasing; `α ≤ L α` | `…HierarchyProof.levelStrict` |
| `LevelBaseRestart` | `D e Γ_0 = D e 0` for `e ≥ 1` | `…HierarchyProof.levelBaseRestart` |
| `LevelCritical` | `D e x` is `N_B`-critical for `e ≥ 1` | `…CriticalProof.levelCritical` |
| `UpperStep` | `ζ + Ω^e ≤ Ω^Ω`, `NormSeparated ζ e`, `x` critical, `ψ ζ ≤ x` ⟹ `ψ(ζ + Ω^e) ≤ D e x` | `…PsiProof.upperStep` |
| `LowerStep` | same context, `x ≤ ψ ζ`, and `|ζ| < ψ(ζ+Ω^e)`, `e < ψ(ζ+Ω^e)` ⟹ `D e x ≤ ψ(ζ + Ω^e)` | `…PsiProof.lowerStep` |

## What is NOT claimed

- No closed formula for ψ on `[Ω, Ω^Ω)`; no statement about indices above `Ω^Ω`.
- `LowerStep` says nothing when the index is not active (there the collapse stalls; the equality with
  `D e x` is then false in general).
- Nothing about `n ≥ 4`, the endpoint identification with BH, or Simmons's helpfulness at higher types.
- `UpperStep` needs `x` critical (it is false for `e = 0` otherwise, since `ψ(ζ+1)` is critical and
  `N_B x` need not be).
