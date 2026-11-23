# Calibration induction note (Opus A, round 6)

Goal: `Calibration (veblenData fix pow w)`, i.e. `∀ n, Δ_n' = ψ(a_n)`. Status:
- n = 0, 1 proved (#1488).
- n = 2 proved (#1491).
- n = 3: layers T1–T3 gated (below). T4 (`PsiPowerLevel`) and T5 (`CalibrationThree`) are frozen but not proved.

All objects are the repository's semantic ones:
- `N := N_B = veblenValue fix pow`, `Γ := Γ_0 = N(ω)`;
- `orbit` is convention (I);
- `fix f z = f^ω(z+1)`, `B_0 h = fix(α ↦ h^α(0))`, `B_1 H h = fix(α ↦ (H^α h)(0))`;
- ψ is the (P)-collapse on `ξ ≤ Λ` with the coefficient norm (#1486).

## n = 3 layers

| Layer | Statement (`ActualCalibrationThreeTargets`, sha `fe4a54a7…afca`, receipt `1795414855188190708-3319458`) | Status |
|---|---|---|
| T1 `FixLeastAbove` | for `g` monotone, `x ≤ g x`, continuous at limits: `fix g x` is the least fixed point of `g` strictly above `x` | **gated** |
| T2 `B0Lemma` | for monotone inflationary `h` with `ω² ≤ h(ω)`, `B_0 h (h ω)` is the least fixed point of `α ↦ h^α(h ω)` | **gated** |
| T3 `LevelInvariant` | `D β := B_0^β(N)` (`A_1`-orbit) is monotone inflationary for every β, increases pointwise in β, and `D (β+1) x` is the least fixed point above `x` of `E_β := α ↦ (D β)^α(0)` | **gated** |
| T4 `PsiPowerLevel` | for `1 ≤ e` with no fixed point of `L := (β ↦ D β 0)` in `[1, e]`: `ψ(Ω^e) = L(e)` | frozen, **open** |
| T5 `CalibrationThree` | `Δ_3' = ψ(a_3)` | frozen, **open** |

- T1–T3 are in module `ActualCalibrationThreeLevelProof`, receipt `1795414944051898366-3319804`. It compiled 1,568 modules, all rc 0. The module used 1,123,080 KiB; the whole build peaked at 1,132,008 KiB.
- T2 needs the hypothesis `ω² ≤ h(ω)`. **Without it the lemma is false**: for `h = succ`, `B_0 h Γ = Γ + 1`, while the least fixed point of `β ↦ Γ + β` is `Γ·ω`. The hypothesis is what lets `(ω+1) + δ = δ` absorb.
- T3 is really definitional: `D(β+1) = B_0(D β)`, combined with T1 for `E_β`. **Its semantic content is small. The difficulty of n = 3 sits entirely on the ψ side (T4).**

### What T5 needs beyond T4
- `Δ_3' = B_1 B_0 N Γ = fix L Γ` (`towerValue_one`).
- By T1 applied to `L`, this is the least fixed point of `L` above `Γ`. T1 requires `L` to be monotone (T3), continuous at limits (the `A_1`-orbit's pointwise limit clause), and to satisfy `L(α) ≥ α`. The last one is not yet proved: it needs `D(β+1) 0 > D β 0`, i.e. a strict form of T3.
- `ψ(Ω^Ω)` should be the least fixed point of `L` that is `≥ 1`. That follows from T4 by the same two-sided argument as n = 2:
  - an upper bound `ψ(ξ) ≤ M(ξ)` on `[Ω, Ω^Ω)`;
  - lower bounds below the fixed point.

### What T4 needs: the description of ψ on `[Ω, Ω^Ω)`
For `ξ = Ω^e·a + ρ` with `1 ≤ e < Ω`, `1 ≤ a < Ω` and `ρ < Ω^e`, the norm is `|ξ| = max(e, a, |ρ|)`. This uses `|Ω^e| = max(1, e)`; for countable `e ≥ 1` that is `e`.

The expected description is a recursion on the Cantor normal form:
- `ψ(Ω^e·a) = E_e(a)`, the a-th value of level e. Here `E_e(α) = (D e)^α(0)`.
- `ψ(Ω^e·a + ρ)` is the ψ-value of `ρ`, computed one level down but started at `E_e(a)`. For `e = 1` this is `F_0(E_1(a) + ρ)`, with `F_0 = α ↦ N^α(Γ)`.
- Collapse: once an argument (a coefficient, or the norm of an exponent) reaches the value being computed, the value stops growing. This is the n = 2 phenomenon `ψ(η) = δ` for `η ≥ δ`, at every level.

Proving this means a double transfinite induction: on `e`, and on the coefficient and tail. It reuses the n = 2 pattern at each step:
- the upper bound comes from leastness in (P) with an explicit candidate;
- the lower bound comes from closure in (P) and the absence of fixed points below.

The ingredients are:
- T1–T3;
- composition and start-monotonicity of orbits (#1491);
- `|Ω^e·a + ρ| = max(e, a, |ρ|)`: a Cantor-normal-form computation like `norm_countable`;
- the level-e analogue of `OrbitComparison`: `E_e`'s fixed points are those of the enumeration started at the previous level's first value.

Estimated size: about 1–2k lines. T4 is where it goes.

## The level-l invariant, as it should be frozen next
The interval `[a_{l+1}, a_{l+2})` is where the exponents of ξ range over `[a_l, a_{l+1})`. The invariant is an induction on `l`, at type `A_{l+1}`:

1. **Helpful objects** (definition by recursion on the type level k).
   - `Help_1(h)` for `h : A_1`: h is monotone and inflationary (`MonoInfl`), and `ω² ≤ h(ω)`.
   - `Help_{k+1}(H)` for `H : A_{k+1}`: H is pointwise monotone on `Help_k` arguments, `H h ≥ h` pointwise, and `Help_k h → Help_k (H h)`. Higher levels are defined the same way, pointwise along the curried arguments.

   T3 establishes `Help_2(B_0)` in the `MonoInfl` form (`b0_monoInfl`). The `ω²` clause holds for every `D β` because `D β ≥ N` pointwise.
2. **Semantic invariant at level l.** `B_l : A_{l+2}` maps `Help_{l+1}` to `Help_{l+1}`. In addition:
   - Its transfinite orbit `β ↦ B_l^β(H)` (type `A_{l+1}`, pointwise sups at limits) consists of helpful objects and increases in β.
   - **The "next level" clause:** `(B_l H) h⃗ x` is the least fixed point above `x` of `α ↦ (H^α h⃗)(0)`, at every argument tuple `h⃗` of the lower types. T1 gives this verbatim at every type, because `fix` acts only at the last, base, argument.
3. **ψ-correspondence at level l.** This is the open part. There is a map `κ_l` from `[a_l, a_{l+1})` (with its norm) into type-`A_l` objects, built from `B_0, …, B_{l-1}` and `N`:
   - `κ_0 = N`;
   - `κ_{l}(Ω^ζ·a + ρ)` is obtained by applying the a-fold iterate of `κ_{l-1}(ζ)` and continuing with ρ;
   - values below collapse points are given by the same CNF recursion as for n = 3.

   For `ξ ∈ [a_{l+1}, a_{l+2})` with `|ξ|` below the relevant fixed points, the claim is that `ψ(ξ)` is obtained from `κ_l` by the recursion above. The calibration instance is
   `ψ(a_{l+2}) = least fixed point of (ζ ↦ B_l^{ζ}(B_{l-1}) ⋯ (N)(0))`, which is `Δ_{l+2}' = B_l B_{l-1} ⋯ B_0 N Γ`. In other words, `Δ_{l+2}'` is the least fixed point of the level-`l+1` diagonal above `Γ`.
4. **Base and step.**
   - **Base, l = 0:** the n = 2 proof, i.e. T2 together with `calibrationTwo`.
   - **Step:** assume the level-l invariant. Then, for `ξ` with exponents in `[a_l, a_{l+1})`, the (P) clause at `ξ` closes under exactly the values the iterates of `B_l^ζ` produce. Upper bound by leastness; lower bound by closure plus no-fixed-point-below. This is the same two-sided pattern, with "orbit of `N`" replaced by "orbit of `B_l^ζ` at type `A_{l+1}`".
   - The comparison lemma (an orbit started at 0 against one started at `Γ`) is needed at every level. It holds by monotonicity in the start value plus composition, given the `ω²`-type absorption, which every helpful object provides.

This is Simmons 2004 §§5–6 / 2008 §5 in the repository's semantics.

**Why n = 3 is the critical test.** n = 3 is item 3 for `l = 1` restricted to exponents `e < Ω`. Item 3 is also the first place the induction needs `κ`, the correspondence between ordinals and functionals; T1–T3 do not. Once T4 is proved in the CNF-recursive form above, the level-l statement can be frozen with `κ_l` defined by recursion on the hereditary CNF.

## Finding (no obstruction so far)
- The level-1 invariant, in the form T3, is **true** and proved.
- No semantic definition blocks the induction.
- The open work is on the ψ side (T4), not on `B_0`'s semantics.
- The only correction to the statement as first proposed is the `ω² ≤ h(ω)` hypothesis in T2, which is necessary.
