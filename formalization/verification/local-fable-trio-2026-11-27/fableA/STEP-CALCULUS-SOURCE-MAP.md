# Source map — step calculus and level-2 targets (Fable A, 27 November 2026)

Frozen target modules (all in `LogicLineages/NativeModule/PersistentMarking/`, namespace
`LogicLineages.PersistentMarking.ActualCalibrationStep`):

| file | sha256 | first gated in |
|---|---|---|
| `ActualCalibrationStepTargets.lean` | `21778a9d5fb95ff11b0e17737ae331272c2546871700892adc1a6769ae26aa19` | `1795813154779391068-1086911` |
| `ActualCalibrationStepOrbitTargets.lean` | `7577abeca72a815242f52c9aa57d3dc3c0b5b4d2d849c48fc3e41ab35b6329ee` | `1795813662649156533-1089665` |
| `ActualCalibrationLevelTwoTargets.lean` | `b95a575b8f2e640bcd524296aeb128410f0c7cb724512279b501eb10d9ffdfbe` | `1795814001440580672-1091742` |

## What they serve

Paper 16, `sections/ordinals.tex` 552–575 ("`Δ_n = ψ_B(a_n)` by the cited calibration"), i.e. the TARGETS.md
checkpoint `Paper16RemainingOrdinalTargets.AllTowerCalibration`, through root's per-level interface
`ActualCalibrationLevelsTargets` (`LevelFactsAt l`, `PsiTowerLevelAt l`). They are intermediate layers, not paper
statements: the paper cites Simmons 2004 §§5–6 / 2008 Thm 5.10 for the whole calibration.

## Definitions

- `StepContext ζ π`: `ζ + π ≤ Λ` and `|ζ + τ| = max |ζ| |τ|` for `τ < π`.
- `StepUp/StepLow fix pow w π H`: the two halves of "`(π, H)` is a step" (ψ at `ζ + π` against `H x`); `StepLow`
  needs the index to be active (`|ζ|` and `|π|` below its ψ-value).
- `NormPrincipal π`: `|π·c + τ| = max (max c |π|) |τ|` for `1 ≤ c < Ω`, `τ < π`.
- `GoodFn H`: monotone inflationary, `≥ N_B`, critical-preserving. `IsStep ε H`: `GoodFn H` and `(Ω^ε, H)` a step.
- `levelTwo fix e = B_1^e B_0` (tier-2 orbit). `GoodOp G`: good functions to good functions and `B_0 K ≤ G K`.
- `ExpCond ε s`: `NormSeparated ε s ∧ |ε| ≤ |ε + Ω^s| ∧ s ≤ |ε + Ω^s| ∧ Ω^(ε + Ω^s) < Λ`.

## Statements (all proved; receipts in the evidence file)

| name | content | assumptions worth noting |
|---|---|---|
| `StepBase` | `(1, N_B)` is a step | — |
| `StepDiagonal` | diagonal of a family of steps is a step | all family hypotheses explicit (cofinality with norm bound, two norm conditions, monotone/continuous zero-diagonal, closure and criticality of its fixed points, `D x` = least fixed point above `x`) |
| `StepSuccessor` | `(π, H)` step ⟹ `(π·Ω, B_0 H)` step | `NormPrincipal π`, `|π| ≤ |π·Ω|`, `H` good |
| `StepLimit` | supremum of a norm-monotone family of steps is a step | family hypotheses explicit |
| `StepB0Orbit` | `IsStep ε H ⟹ IsStep (ε+e) (B_0^e H)`, `e` countable | `Ω^(ε+Ω) ≤ Λ`, `NormSeparated ε 1` |
| `OpSuccessor`, `LevelTwoGood` | `B_1` preserves good operators; `B_1^e B_0` good, monotone, strictly increasing in `e` | — |
| `OpWeightSuccessor` | `G` adds `Ω^e` to step exponents ⟹ `B_1 G` adds `Ω^(e+1)` | `e` countable; `GoodOp G` |
| `LevelTwoWeight` | `IsStep ε H ⟹ IsStep (ε + Ω^e) (B_1^e B_0 H)` | `ExpCond ε e`, `e` countable |

## What is NOT claimed

- Nothing at type `A_3` or above (`B_2`, levels `l ≥ 3`); no uniform-in-`l` statement is frozen.
- `OpWeightSuccessor`/`LevelTwoWeight` are for countable weights `e` only; level 3 needs them for weights below `Ω^Ω`.
- No closed formula for ψ; `StepLow` is silent at inactive indices.
- `calibrationAt_four` uses root's `exact_CalibrationStep` (receipt `1795778069541429314-942177`).
