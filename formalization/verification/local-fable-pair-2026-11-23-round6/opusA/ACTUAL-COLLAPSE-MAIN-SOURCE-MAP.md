# ACTUAL-COLLAPSE-MAIN: source map (Opus A, round 6)

The conditional Paper 16 statements are re-closed on the actual collapse data `veblenData fix pow w` (#1486). There,
`TowerHypotheses` is a theorem (`actualTowerHypotheses`), so **the hypothesis list shrinks from five to four**.

## Gated

| Module (`LogicLineages/NativeModule/PersistentMarking/`) | sha256 | Receipt |
|---|---|---|
| `ActualCollapseMainTargets` (frozen; compiled alone) | `aa31516edce9ce79067e1bda2466de7fc1ff99b1c49b3b15722f164b44a1ef31` | `1795413729690514195-3315280` |
| `ActualCollapseMainProof` | `b31310ad8f156e2f2db7c31040729e516d429aee931fb1503765644e5feb11cf` | `1795413791081556546-3315542` (2,232 modules, all rc 0) |

- Theorems: `solutionExists`, `actualTowerCofinality`, `actualHeightEffective`, `actualMain16`,
  `calibrationFirstInstances`.
- Axioms for all five: `[propext, Classical.choice, Quot.sound]`.
- Peak RSS: 1,185,272 KiB.

## Statements

- **`actualTowerCofinality`** (`lem:tower-cofinality` on the actual data):
  - `⨆ n, ψ(a_n) = ψ(Λ)` outright;
  - `= BH` under `BHIdentification (veblenData …) BH` alone.
- **`actualHeightEffective`** (`thm:height`, effective form #1470). Hypotheses: `Calibration (veblenData …)`,
  `BHIdentification (veblenData …) BH`, `UpperBound BH`.
- **`actualMain16`** (Paper 16 `thm:main`, the external agent's uniform coded-effective form #1477, which includes the
  `Primrec` tower code). Exactly four hypotheses:
  1. `ExternalOrdinalInterfaceID1Targets.NormTheorem BH` (E4, Pohlers)
  2. `ConditionalUpperUniformTargets.UniformAccessibility` (R1, internal ID₁)
  3. `Calibration (veblenData fix pow w)` (E1, Simmons)
  4. `BHIdentification (veblenData fix pow w) BH` (E3, Pohlers §§9.4–9.5)
- **Quantification over solutions.** Every statement holds for *every* solution `(Z, s, add, mul, w, one, pow, fix)` of
  the arithmetic and ω equations; any one solution yields the conclusion.
  - Solutions exist unconditionally: `solutionExists`, from `exact_OrdinalArithmeticOrbits` and
    `exact_OrdinalOmegaOrbits`.
  - The equations fix `s`, `w`, `pow` and `fix` as functions, so `veblenData` is the same object for every solution.

## Calibration on the actual data: one line
`Calibration (veblenData fix pow w)` ⟺ for some solution, `∀ n, (sequenceValue fix pow w n).val = collapse actualNorm
(Critical N_B Γ_0) ⟨argument n, _⟩`. Here `Δ_n'` (#1462) is the paper's composite of the semantic `B_l`, Next and ω,
and the right side is the (P)-collapse at `a_n`.

## First instances: proved (`calibrationFirstInstances`)
- **n = 0.** `Δ_0' = ε_B = N_B(ω) = Γ`, and `ψ(0)` is the least critical value (the clause is vacuous), which is
  `Γ = N_B^0(Γ)`. So `Δ_0' = ψ(a_0)` holds by definition.
- **n = 1.** `Δ_1' = N_B(Γ)`. `ψ(1)` is the least critical θ with `ψ(0) = Γ < θ`, since `|0| < θ` (critical values
  exceed 1). The orbit is strictly increasing because `N_B` is inflationary, so this is `N_B^1(Γ) = N_B(Γ)`. Hence
  `Δ_1' = ψ(a_1)`.

## n = 2 and the general step: not a consequence of the definitions
- **The two sides at n = 2.**
  - Left: `Δ_2' = B_0 N_B Γ_0 = Fix(λα. N_B^α(0))(Γ_0) = g^ω(Γ_0+1)` with `g(α) = N_B^α(0)`. This is an orbit of
    `N_B` started at **0**, as the terminal Z prescribes, iterated by α and then closed by the ω-iteration of `fix`.
  - Right: `ψ(a_2) = ψ(Ω)`. For countable η, `|η| = η`, since the base-Ω normal form is `[(0, η)]`. So `ψ(Ω)` is the
    least critical θ with `ψ(η) < θ` for every countable `η < θ`, where `ψ` on countable η enumerates the orbit
    `N_B^η(Γ_0)` (with collapsing once η passes the values).
- **Equating them needs two facts about the semantic `N_B`.** Neither (P) nor the definitions supply them:
  1. **Order and continuity properties of `N_B`.** It must be monotone and continuous in the relevant sense, so that
     `α ↦ N_B^α(x)` is normal and its iterated fixed points are the closure points. The repository proves only that
     `N_B` is inflationary.
  2. **The comparison of orbits started at 0 and at `Γ_0 = N_B(ω)`.** We need `N_B^α(0)` against `N_B^α(Γ_0)` (for
     example `N_B^{1+α}(0)` against `N_B^α(N_B(ω))`), which depends on the values of `N_B` at small arguments.
- **This is Simmons's helpfulness of `B_0`, `B_1` (2008 Thm 5.10)** together with the identification of the Fix /
  iterate fixed points with the hull collapse (2004 Thm 6.1 / Cor 6.2). The general step `Δ_{n+1}' = ψ(Ω^{a_n})` is
  that theorem for `B_{n-1}` at every level: helpfulness of every `B_l`, and the tameness condition the paper checks.
- **Verdict.**
  - The calibration's first two instances are definitional, and are now gated.
  - The first non-definitional instance is n = 2. It already needs a monotonicity/continuity analysis of the semantic
    `N_B`, which is the helpfulness content.
  - Formalizing next: prove `N_B` monotone and continuous from the #1462 semantics, then attempt `Δ_2' = ψ(Ω)`. If that
    closes, the inductive step over `B_l` is Simmons's Thm 6.1 pattern applied uniformly.
