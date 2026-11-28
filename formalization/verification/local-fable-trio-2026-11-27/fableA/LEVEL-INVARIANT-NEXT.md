# The level-l induction for `AllTowerCalibration`, after n = 3 (Fable A, 27 November 2026)

Status: n = 0, 1, 2, 3 proved (`calibrationThree`, receipt `1795777959277796293-941615`). This note says
what n = 3 taught and which statements should be frozen next. Everything below the line "Proved" is
proved and gated; everything under "Proposed" is mathematics on paper, not yet Lean, and is marked with
how sure I am.

## 1. What n = 3 actually used (proved)

The round-6 note expected a description of ψ on `[Ω, Ω^Ω)` by a Cantor-normal-form recursion `κ_l`.
That is not needed. The proof has three parts, and only the third is specific to n = 3.

1. **Generic collapse facts** (any (P)-collapse): ψ is weakly monotone; *stall*: if every index in
   `[ζ, ξ)` has norm `≥ ψ ζ` then `ψ ξ = ψ ζ`. Stall is the whole "collapse phenomenon": an index is
   *active* when its norm is below its own ψ-value, and everything after an inactive index up to the next
   index of small norm has the same value.
2. **A step notion.** Call `(π, H)` — `π` an ordinal, `H : A_1` — a *step* when, for every context `ζ`
   with `ζ + π ≤ Λ` and `|ζ + τ| = max(|ζ|, |τ|)` for `τ < π` (`NormSeparated`):
   - (Up) `x` critical, `ψ ζ ≤ x` ⟹ `ψ(ζ + π) ≤ H x`;
   - (Low) `x ≤ ψ ζ`, and `|ζ|`, `|π|` below `θ := ψ(ζ + π)` ⟹ `H x ≤ θ`.
   `UpperStep`/`LowerStep` say: **`(Ω^e, B_0^e N_B)` is a step for every countable `e`.**
   The proof is an induction on `e` whose three cases are three closure properties of steps:
   - (S0) `(1, N_B)` is a step (criticals are the `N_B`-orbit of `Γ_0`).
   - (S1) *diagonal over composites*: if `(π, H)` is a step then `(π·Ω, B_0 H)` is one. Inside: the
     composite `(π·a, H^a)` is a step for every countable `a` (chain), and the diagonal over `a` gives the
     least fixed point of `a ↦ H^a(0)` above `x`, which is `B_0 H x`.
   - (S2) *limits*: if `(π_β, H_β)`, `β < l`, are steps, increasing, with `|τ| ≥ |π_β|` for
     `τ ∈ [π_β, π_l)`, then `(sup π_β, pointwise sup H_β)` is a step.
   Function-side inputs: `H` monotone inflationary; `y + y ≤ H y` (from `H ≥ N_B` and `VeblenDoubling`);
   `H` maps criticals to criticals; positive fixed points of `a ↦ H^a(0)` are limits closed under `+`,
   under `H` and under `H`-orbits.
3. **The top diagonal** (root's `CollapseDiagonal.exact_DiagonalCollapse`): from `ψ(Ω^e) = L e` below the
   first fixed point of `L` to `ψ(Ω^Ω) = ` least fixed point of `L` above `Γ_0`.

One correction to the round-6 note: T3 was called "semantically small". True, but the function side still
needed about 300 lines that were not in T1–T3: doubling of `N_B`, additive closure of the fixed points of
`E_β`, criticality of the values of `D e`, and `D e Γ_0 = D e 0`. All of these are consequences of
"`H ≥ Next` pointwise" plus monotonicity; none is specific to level 1.

## 2. Root's question: does the general step fit `CollapseDiagonal.DiagonalHypotheses`?

**Yes, at the top of every level.** For `l ≥ 0` put
- `top = a_{l+3}`, `p e = towerIndex (l+1) e` (root's `ActualTowerIndex`; `exact_TowerIndexFacts` gives
  `below`, `norm`, `cover`),
- `L_{l+1} e = (B_l^e B_{l-1}) B_{l-2} ⋯ B_0 N_B 0` (orbit of `B_l` at type `A_{l+1}` from `B_{l-1}`, applied
  down the tower; for `l = 0` it is `(B_0^e N_B) 0`, the present `L`).

Then `Δ_{l+3}' = B_{l+1} B_l ⋯ B_0 N_B Γ_0 = fix L_{l+1} Γ_0`, and `exact_DiagonalCollapse` yields
`ψ(a_{l+3}) = Δ_{l+3}'` from exactly four inputs:

| field | what it needs | status |
|---|---|---|
| `level` | **T4 at level l+1**: `ψ(towerIndex (l+1) e) = L_{l+1} e` below the first fixed point of `L_{l+1}` | open for `l ≥ 1`; the real work (§3) |
| `strict`, `inflationary`, `noEarlyFixed` | `L_{l+1}` strictly increasing and `Γ_0 < L_{l+1} 1` | open for `l ≥ 1`: needs monotonicity of `B_l` at type `A_{l+2}` (Simmons's helpfulness, 2008 Thm 5.10, in the repository's semantics). For `l = 0` it is `exact_LevelFacts` |
| `limit` | orbit equations at tier `l+1` (pointwise sup) | definitional, as for `l = 0` |
| `Δ' = fix L Γ`, least fixed point | a general unfolding `towerValue φ (l+1) h h_{l+1} ⋯ h_1 = φ(α ↦ (h^α h_{l+1}) h_l ⋯ h_1 0)` (only `towerValue_zero`, `towerValue_one` exist) and T1 | open, routine (`curryEnv` induction) |

So: **the general calibration reduces to the level-(l+1) analogue of T4, plus higher-type monotonicity of
`B_l`, plus one unfolding lemma.** Sanity check at `e = 1`, `l = 1`: `ψ(Ω^Ω) = (B_1 B_0) N_B 0`, which is
`calibrationThree` with start `0` instead of `Γ_0` (equal, since the least fixed point of `L` above `0`
exceeds `Γ_0`).

Caveat on the norm field: `DiagonalHypotheses.norm` wants `|p e| ≤ e`; fine for `towerIndex`. But the
*inner* diagonals of §3 are not of this shape (they run inside a context `ζ` and start from an arbitrary
`x`), so `exact_DiagonalCollapse` cannot be reused for them; S1 above is the contextual version.

## 3. Proposed: the invariant that proves T4 at every level

Confidence: the shape is right (it reproduces `a_4 = Ω^(Ω^Ω)` for `Δ_4'` below and specializes to the gated
n = 3 proof); the exact side conditions (separation and activity at higher types) are **not yet checked
on paper in full** and must be before freezing.

The level functions carry *ordinal weights*, by type:

- type `A_1`: `H` has weight `π` when `(π, H)` is a step (§1). Weight acts on contexts by `ζ ↦ ζ + π`.
- type `A_2`: `G` has weight `δ` when it maps every step `(π, H)` (with `π = Ω^ε`, `ε` separated from
  `δ`) to a step `(π·Ω^δ, G H)`. S1 says: **`B_0` has weight 1.**
- type `A_{k+1}`, `k ≥ 2`: `Φ` has weight `σ` when it maps every `A_k`-object of weight `t` to one of weight
  `t·Ω^σ`.
- **Claim (W):** `B_k` has weight 1 at type `A_{k+2}`, for every `k`.

Check: `N_B` has weight 1. `B_0 N_B`: `Ω`. `B_1 B_0` has weight `1·Ω^1 = Ω` (type `A_2`), so
`(B_1 B_0) N_B` has weight `1·Ω^Ω = Ω^Ω = a_3`. `B_2 B_1`: weight `Ω` at type `A_3`, so `B_2 B_1 B_0` has
weight `1·Ω^Ω` at type `A_2`, and `(B_2 B_1 B_0) N_B` has weight `Ω^(Ω^Ω) = a_4`. In general
`B_l ⋯ B_0 N_B` has weight `a_{l+2}`, and "weight `π`" applied at the empty context with `x = Γ_0 = ψ 0`
is `ψ(a_{l+2}) = Δ_{l+2}'` — provided the index is active, which is where the no-fixed-point hypothesis
of T4 and the top diagonal enter. T4 at level `l+1` is the same statement for the orbit
`B_l^e B_{l-1}` (weight `Ω^e` at type `A_{l+1}`), i.e. for `towerIndex (l+1) e`.

Why (W) should hold: `(B_k Φ) G ⋯ = fix(a ↦ (Φ^a G) ⋯ 0)`. If `Φ` has weight `σ` then `Φ^a G` has weight
`t·Ω^(σ·a)` (successor: definition of weight; limit: S2 one type up), and the diagonal over `a < Ω` has
weight `t·Ω^(σ·Ω)`. So `B_k Φ` has weight `σ·Ω`: `B_k` multiplies the weight of its argument by `Ω = Ω^1`.
Each instance is **one diagonal lemma (DL)**, the common generalization of S1 and of root's diagonal:

> (DL) Let `(π_a, K_a)`, `1 ≤ a < Ω`, be steps, increasing in `a`, continuous at limits (`π` and `K`
> pointwise), with `max(c, a) ≤ |ζ + π_a + τ|`-type norm bounds for a fixed `c`, and such that every
> positive fixed point `κ` of `a ↦ K_a(0)` satisfies `a, x < κ ⟹ K_a(x) < κ`. Then
> `(sup_a π_a, x ↦ least fixed point of a ↦ K_a(0) above x)` is a step.

In S1, `K_a = H^a` and the closure hypothesis is "start-monotone + composition + additive closure". At the
next type, `K_a = (G^a H)` and the closure hypothesis follows from
`(G^a H)((G^b H) 0) ≤ (G^m H)^2(0) ≤ (B_0 (G^m H)) 0 ≤ (G^(m+1) H) 0`, `m = max(a, b)`, which needs
"`G K ≥ B_0 K` pointwise for the `G` that occur" — a helpfulness-type fact.

Known trap (found while checking S2 for uncountable exponents): the norm is **not** monotone along
arbitrary exponents (`|Ω + 5| = 5 > 2 = |Ω·2|`), so S2 and DL must carry the hypothesis
"`|τ| ≥ |π_β|` for `τ ∈ [π_β, π_l)`" explicitly; it holds along the families that occur
(`ε_0 + e`, `ε_0 + Ω^e·a` with `ε_0` separated), by the same computation as `norm_ge_of_mul_le`.

## 4. Suggested order of work (each a freezable layer)

1. **Step calculus at type `A_1`** (re-proof of the gated n = 3 argument with `N_B` replaced by an
   arbitrary step function): definitions `IsStep π H`; theorems S1 (`IsStep π H → IsStep (π·Ω) (B_0 H)`),
   S2 (limits, with the norm-monotonicity hypothesis), and hence
   `IsStep (Ω^ε) H → IsStep (Ω^(ε+e)) (B_0^e H)`. Function-side hypotheses to bundle with `IsStep`:
   `MonoInfl H`, `H ≥ N_B` pointwise, `H` maps criticals to criticals. Expected size: the present
   `…PsiProof` (≈ 330 lines) plus a general `norm_leading` for uncountable exponents
   (`|Ω^ε·c + τ| = max(max(c, |ε|), |τ|)`, same proof, without `norm_countable`). Low risk.
2. **DL** as stated, and **weight at type `A_2`**: `B_1 G` has weight `δ·Ω` when `G` has weight `δ`.
   This yields T4 at level 2 (`ψ(Ω^(Ω^e)) = (B_1^e B_0) N_B 0`) and, with root's diagonal, n = 4. Medium
   risk: the separation/activity conditions for exponent contexts have to be fixed here; n = 4 is the
   test that they are right.
3. **Uniform (W)**: recursion on the tier for "weight", `B_k` has weight 1. High risk in Lean
   (`Value (tier k)` dependent types; the definition of weight at type `A_{k+1}` quantifies over all
   weighted objects one type down, i.e. a logical relation), low mathematical risk once step 2 is done,
   because step 2 → 3 repeats the same argument.
4. **Higher-type monotonicity** of `B_l` (for `strict`/`noEarlyFixed` of `L_{l+1}`) and the general
   `towerValue` unfolding. Independent of 1–3; can be done in parallel.

What I would *not* do: describe ψ by normal forms, or try to prove (W) directly by induction on `l` at the
level of indices. The weights compose multiplicatively at types `≥ A_2` and additively at `A_1`, and the
only analytic content is DL.
