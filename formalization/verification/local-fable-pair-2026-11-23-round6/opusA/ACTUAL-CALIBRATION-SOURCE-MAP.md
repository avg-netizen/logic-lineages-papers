# ACTUAL-CALIBRATION: source map (Opus A, round 6)

This covers the calibration `Δ_n' = ψ(a_n)` on the actual data: monotonicity of the semantic functionals, the orbit
comparison, and the first non-definitional instance n = 2. **n = 2 is proved.**

Everything here is about the repository's semantic `N_B = veblenValue fix pow` (#1462) and the (P)-defined collapse
(#1486). It replaces a citation to Simmons only for the literal instances of `Calibration` it proves: n = 0, 1 (#1488)
and n = 2 (here).

## Gated (`LogicLineages/NativeModule/PersistentMarking/`)

| Layer | Module | Theorems | sha256 | Receipt |
|---|---|---|---|---|
| targets (frozen; compiled alone) | `ActualCalibrationTargets` | `MonoInfl`, `MonotoneLayer`, `OrbitComparison`, `CalibrationTwo` | `67164767482f8bb91c4b391231a43cab4ccbbffcb8aee7b47f4718820c66c466` | `1795414149544123977-3316676` |
| 1 monotonicity | `ActualCalibrationMonotoneProof` | `countable_induction`, `orbit_start_mono`, `orbit_compose_le`, `fix_monoInfl`, `fix_ge_stage_one`, `next_monoInfl`, `b0_monoInfl`, `b0Orbit_mono`, `veblen_monoInfl`, `monotoneLayer` | `77cc39dcda04816781c4e6dd41aa4b851567c4db43517c5bdf0efa931b0a39f1` | `1795414267122070603-3317173` |
| 2 comparison | `ActualCalibrationComparisonProof` | `orbitComparison` | `fd0325e8de3080f3834be2337028b25c4fa3f4e6c6bdd4fd679cdf6460a13b0a` | `1795414344456309033-3317393` |
| 3 n = 2 | `ActualCalibrationTwoProof` | `norm_countable`, `calibrationTwo` | `69d2b8bbb20f7ea94fa2b95d0b2e23e1aee759aa8daec0724c7b6e8a6f6972ab` | `1795414486482435704-3317900` (1,566 modules, all rc 0) |
| checks | `ActualCalibrationChecks` | `exact_MonotoneLayer`, `exact_OrbitComparison`, `exact_CalibrationTwo` | `7f4d7ece9f32d867d78a29383e9f478d3a74670dacfefcfda5d34c7326c6bfe7` | `1795414527299825250-3318034` |

- Axioms: all `[propext, Classical.choice, Quot.sound]`.
- Peak RSS: 1,132,008 KiB, at `ActualCalibrationTwoProof`.

## Layer 1: which functionals are monotone
- **Monotone (∀ x ≤ y, f x ≤ f y) and strictly inflationary**:
  - `Next = fix pow`;
  - `B_0 h` for every monotone inflationary `h`, with `h ≤ B_0 h` pointwise;
  - every stage of the `A_1`-orbit `β ↦ B_0^β(Next)`, which is also pointwise monotone in `β`;
  - `N_B`.
- **`fix f`** is monotone and inflationary for every *monotone* `f`. Inflation of `fix f` needs nothing of `f`.
- **Generic orbit facts:**
  - start-monotonicity needs only `f` monotone;
  - `f^β(f^α(x)) ≤ f^{α+β}(x)` needs `f` monotone and inflationary.
- **Not monotone in general: the iteration convention (I) itself.** `thm:iteration` allows any `f`, and nothing here
  claims `α ↦ f^α(x)` is monotone unless `f` is inflationary. The functionals the tower actually feeds in are all
  monotone and inflationary, so this is not a counterexample to anything used.
- **Finding: continuity is false.** `Next(z)` is the least epsilon number above `z`:
  - `Next(ε_0) = ε_1`;
  - but `sup_{z<ε_0} Next(z) = ε_0`.

  So `Next` is not continuous. `N_B` similarly fails to be continuous ("strictly inflationary", in the paper's words).
  None of the arguments needs continuity of the iterated function. They use only the limit clause of the orbit itself,
  which is continuous in the stage by definition.

## Layer 2: the comparison
`OrbitComparison`: `N_B^β(Γ_0) ≤ N_B^{(ω+1)+β}(0)`. The proof:
- `Γ_0 = N_B(ω) ≤ N_B(N_B^ω(0)) = N_B^{ω+1}(0)`, using `N_B^ω(0) ≥ ω` and monotonicity;
- then start-monotonicity and composition.

## Layer 3: `Δ_2' = ψ(Ω)` (`calibrationTwo`)
Notation:
- `F(β) = N_B^β(Γ_0)` is the critical enumeration.
- `G(α) = N_B^α(0)`.
- `δ = Δ_2' = B_0 N_B Γ_0 = G^ω(Γ_0+1)`.

Steps:
1. `G(δ) ≤ δ`. If δ is a limit, use the orbit limit clause; otherwise the ω-sup is attained.
2. `δ ≥ Γ_0 ≥ Next(0) ≥ ω^ω ≥ ω²`, using monotonicity of the `B_0`-orbit stage.
3. Hence `(ω+1)+δ = δ`, and `F(δ) ≤ G(δ) ≤ δ`. So `F(δ) = δ`, and δ is critical.
4. `F` has no fixed point below δ. Such a θ would be a fixed point of `G` above Γ_0, hence ≥ δ.
5. On countable indices `|η| = η` (`norm_countable`). By induction, `ψ(η) ≤ F(η)` always, and `F(η) ≤ ψ(η)` for η < δ.
6. (P) at Ω then gives `ψ(Ω) = δ`.

## What would give `Calibration` for all n
- **The statement** is literally `Calibration (veblenData fix pow w)`: `∀ n, (sequenceValue fix pow w n).val =
  collapse actualNorm (Critical N_B Γ_0) (a_n)`. Instances n = 0, 1, 2 are now theorems.
- **n = 2 reused as a general lemma.** The n = 2 argument generalizes, with no new idea, to a "B_0 lemma": for every
  monotone inflationary `h` with `h(ω) = Γ`, `B_0 h Γ` is the least fixed point of `α ↦ h^α(Γ)`.
- **Where a new argument is first needed: n = 3**, `Δ_3' = B_1 B_0 N_B Γ_0`.
  - `B_1` iterates `B_0` transfinitely: `B_0^α(N_B)`, at type `A_1`.
  - On the ψ side, `ψ(Ω^Ω)` must be computed from ψ on all of `[Ω, Ω^Ω)`, that is on `Ω·α + β`, whose norms are
    `max(α, β, …)`.
  - Matching them needs an invariant over *all* arguments of `B_0`: for each "level" function `h` (the enumeration of
    the fixed points of the previous level), `B_0 h` enumerates the next level, and the ψ-values on `Ω·α + β` are those
    levels. This is Simmons's helpfulness (2008 Thm 5.10) together with 2004 Thm 6.1, specialized to l = 1.
- **The general step** is that invariant by induction on `l` at type `A_l`: `B_l` maps "helpful" type-`A_{l+1}`
  functionals to helpful ones, and the ψ-values on `[a_{l+1}, a_{l+2})` are their iterates.
- **Size estimate.**
  - n = 2 took about 250 lines on top of the collapse layer.
  - n = 3, the first use of the `A_1`-level invariant, is on the order of 1–2k lines.
  - All n — a typed helpfulness invariant with its ψ-correspondence on hereditary Cantor normal forms, by induction
    on `l` — is several thousand lines, roughly 3–10k, and weeks of focused work.
  - It is a formalization of Simmons 2004 §§5–6 with 2008 §5. It is not assembly.
