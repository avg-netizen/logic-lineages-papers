# Level-l note (Fable A, 27 November 2026) — root's indexing

Root's interface (`ActualCalibrationLevelsTargets`): `levelDiagonal l α = (B_{l-1}^α B_{l-2}) ⋯ N_B 0`
(`l = 1`: `B_0^α(N_B)(0)`), index family `towerIndex l e` (`Ω^e`, `Ω^(Ω^e)`, …), and
`AllTowerCalibration ⟸ ∀ l ≥ 1, LevelFactsAt l ∧ PsiTowerLevelAt l`.
Level 1 is proved and bridged (`levelFactsAt_one`, `psiTowerLevelAt_one`, receipt `1795778199692925204-942837`).
Everything in §1–§3 is argument on paper; nothing in it is Lean yet. Confidence is stated per item.

## 1. Verdict on `PsiTowerLevelAt 2`: true as stated (confidence: high, not machine-checked)

Statement: for countable `e ≥ 1` with no fixed point of `L_2 := levelDiagonal 2 = (e ↦ (B_1^e B_0) N_B 0)` in
`[1, e]`: `ψ(Ω^(Ω^e)) = (B_1^e B_0) N_B 0`.

- `e = 1`: `(B_1 B_0) N_B 0 = fix L_1 0` = least fixed point of `L_1` above `0`; every positive fixed point of
  `L_1` exceeds `Γ_0` (`base_lt_level`), so this is the least fixed point above `Γ_0`, i.e. `Δ_3' = ψ(Ω^Ω)`
  by `calibrationThree`. The guard at `e = 1` is vacuous (`L_2 1 ≠ 1`). ✓
- limit `e`: `L_2 e = sup_{e'<e} L_2 e'` (tier-2 orbit, pointwise), and on the ψ side the tower-cofinality
  argument: an index below `Ω^(Ω^e)` with norm below `sup L_2 e'` lies below some `Ω^(Ω^(e'))` with norm
  below `ψ` of it. Needs the guard only to know `e' < L_2 e'` (activity of `Ω^(Ω^(e'))`, whose norm is `e'`). ✓
- successor `e = e'+1`: `(B_1 G) N_B 0` with `G = B_1^(e') B_0` is the least positive fixed point of
  `a ↦ (G^a N_B) 0`; on the ψ side the indices are `Ω^(Ω^(e')·a)`, and the diagonal lemma of §2 applies.
- The guard is the right one, for the same reason as at level 1: it is equivalent (by induction on `e`) to
  activity `e' < ψ(Ω^(Ω^(e')))` for all `1 ≤ e' ≤ e`, and it is necessary (at a fixed point `λ = L_2 λ < e`
  the collapse stalls at `λ`). No guard on the *lower* diagonals is needed: activity of every intermediate
  index follows from activity of the top index by the stall lemma, because the norm is monotone along
  each family that occurs (§2, F-norm-low2).

What could still be wrong: only the bookkeeping of norm separation for exponent contexts (the hypothesis
written `Sep` below). If it fails, the fix is in the context conditions of the inner statements, not in
`PsiTowerLevelAt`.

## 2. The analytic core: steps and one diagonal lemma (type `A_1`)

A *step* is a pair (`π` ordinal, `H : A_1`) with, for every context `ζ` such that `ζ + π ≤ Λ` and
`|ζ + τ| = max(|ζ|, |τ|)` for all `τ < π`:

- (Up) `x` critical, `ψ ζ ≤ x` ⟹ `ψ(ζ + π) ≤ H x`;
- (Low) `x ≤ ψ ζ`, `|ζ| < θ`, `|π| < θ` for `θ := ψ(ζ + π)` ⟹ `H x ≤ θ`.

Proved instances (gated): `(Ω^e, B_0^e N_B)` for countable `e` — `upperStep`, `lowerStep`.

**Diagonal lemma DL.** Let `(π_a, K_a)`, `a < Ω`, be steps and `π_Ω` an ordinal with
- (F-cof) `π_a < π_Ω`, and every `τ < π_Ω` lies below `π_{a+1}` for some `a ≤ |τ|`;
- (F-norm-low1) `|π_a| ≤ max(|π_Ω|, a)`; (F-norm-low2) `|τ| ≥ |π_a|` for `τ ∈ [π_a, π_Ω)`;
- (F-fun) `a ↦ K_a(0)` monotone, `a ≤ K_a(0)`, continuous at limits; `K_a` monotone in `a` and in the argument;
- (F-cl) every positive fixed point `κ` of `a ↦ K_a(0)` is a limit and `a, x < κ ⟹ K_a(x) < κ`;
- (F-crit) every such `κ > Γ_0` is critical.

Then `(π_Ω, x ↦ least fixed point of a ↦ K_a(0) above x)` is a step.

Proof = the successor cases of `upperStep`/`lowerStep` read abstractly (Up: leastness with `κ`, F-cof,
`Up_{a+1}`, F-cl. Low: for `a < θ` closure gives `ψ(ζ + π_a) < θ` by F-norm-low1; `(ζ, π_a)` is active by
stall and F-norm-low2; `Low_a` gives `K_a(x) < θ`; `θ` is a limit by the `N_B`-doubling argument; so `θ` is
a fixed point above `x`). Root's `exact_DiagonalCollapse` is DL at the empty context with `x = Γ_0`.

Two families, same lemma:
- composites of one step: `π_a = π·a`, `K_a = H^a`; DL gives the step `(π·Ω, B_0 H)` (F-cl from
  start-monotonicity + composition + additive closure — `enumFix_*`);
- an orbit one type up: `π_a = Ω^(ε + Ω^s·a)`, `K_a = Φ^a G`; DL gives the step
  `(Ω^(ε + Ω^(s+1)), (B_1 Φ) G)` (F-cl from `K_a(K_b 0) ≤ K_{max(a,b)+1}(0)`, which holds when
  `Φ K ≥ B_0 K` pointwise).

## 3. The uniform induction-loading statement

Weights by type level, as a logical relation (`k ≥ 1`; `Help_k` = the hereditary function-side
conditions: monotone, inflationary, `≥ N_B`, critical-preserving at type 1; pointwise the same after
application, and "dominates `B_0`" at higher types):

- `R_1(ε, H)` :⟺ `(Ω^ε, H)` is a step and `Help_1 H`.
- `R_{k+1}(s, Φ)` :⟺ `Help_{k+1} Φ` and for all `(ε, G)` with `R_k(ε, G)` and `Sep(ε, s)`:
  `R_k(ε + Ω^s, Φ G)`.

(So a type-`(k+1)` object of weight `s` adds `Ω^s` to the weight of its argument; at type 1 the weight
`ε` adds `Ω^ε` to the index. `Sep(ε, s)`: the norm of `ε` separates from what is added below `Ω^(s+1)`.)

**Uniform statement (W): for every `k`, `R_{k+2}(0, B_k)`** — `B_k` adds `Ω^0 = 1` to the weight of its
argument: `R_{k+1}(s, Φ) ⟹ R_{k+1}(s+1, B_k Φ)`. Base: `R_1(0, N_B)`.

Consequences, by unfolding the relation along the tower: `B_{l-1}^e B_{l-2}` has weight `e` at type
`A_l` (orbit: successor by (W), limit by closure of `R` under norm-monotone pointwise suprema), hence
`(B_{l-1}^e B_{l-2}) B_{l-3} ⋯ B_0 N_B` has weight `Ω^(Ω^(⋯^e))` = exponent of `towerIndex l e`, and the step
at the empty context with `x = 0` / `x = Γ_0` is `PsiTowerLevelAt l` (activity from the guard, as in
`psiO_power`). `LevelFactsAt l` is the `Help` part.

Proof of (W) at level `k`: for `R_{k+1}(s, Φ)` and `R_k(ε, G)`, the orbit `a ↦ (ε + Ω^s·a, Φ^a G)` stays in
`R_k`; `(B_k Φ) G = λh⃗. fix(a ↦ (Φ^a G) h⃗ 0)` is its diagonal; and "diagonals of good families stay in
`R_k`" is DL_k, which follows from DL (= DL_1) by induction on `k`: unfold `R_{k+1}` once, apply both sides
to an argument `(ε'', G'') ∈ R_k`, and observe that `a ↦ ε'' + Ω^(ε_a)` is again a good family
(F-cof, F-norm-low1/2 are stable under `ε ↦ ε'' + Ω^ε` given separation) and that the diagonal commutes
with application. So the only analytic lemma is DL; the rest is the logical relation.

## 4. Order of work and state

1. **Type-1 step calculus, abstract** — definitions `StepUp`, `StepLow`, and DL as a theorem about an
   arbitrary family; re-derive `(π·Ω, B_0 H)` from it. *In progress this round (targets
   `ActualCalibrationStepTargets`).*
2. Norm calculus for uncountable exponents: `|Ω^ε·c + τ| = max(max(c, |ε|), |τ|)` for `ε` below the
   index (same proof as `norm_leading` without `norm_countable`), the exponent-level versions of
   `norm_div_le` / `norm_ge_of_mul_le`, and stability of F-cof / F-norm-low under `ε ↦ ε'' + Ω^ε`.
3. `Help_2` for `B_1^e B_0` (monotone in the function argument, `Φ K ≥ B_0 K`, orbit monotone) —
   gives `LevelFactsAt 2`.
4. Level 2: `R_2(e, B_1^e B_0)` from DL with the second family; `PsiTowerLevelAt 2`; `n = 4`.
5. Uniform (W): `Value (tier k)`-recursive definitions of `Help_k`, `R_k`, good families; DL_k by
   induction. Lean risk is in the dependent types, not the mathematics.

## 5. Addendum after level 2 was gated (same day)

Proved and gated since §1–§4 were written (receipts in `LEDGER.md` Entries 7–11):
`stepBase`, `stepDiagonal` (DL exactly as in §2), `stepSuccessor`, `stepLimit`, `stepB0Orbit`; at type `A_2`
`opSuccessor`, `levelTwoGood`, `opWeightSuccessor`, `levelTwoWeight`; and `psiTowerLevelAt_two`,
`levelFactsAt_two`, `calibrationAt_four`. So §1's verdict is now a theorem, and the scheme of §3 is confirmed
at `k = 1` (`R_2(e, B_1^e B_0)` for countable `e` is `levelTwoWeight`).

What level 2 taught about the uniform statement (corrections to §3):

1. **The context condition** is not just separation. `Sep(ε, s)` in §3 must be
   `ExpCond ε s := NormSeparated ε s ∧ |ε| ≤ |ε + Ω^s| ∧ s ≤ |ε + Ω^s| ∧ Ω^(ε+Ω^s) < Λ`:
   the two middle clauses say that adding `Ω^s` does not *lower* the norm (it can, when `ε` has a tail below
   `Ω^s`), and they are what the diagonal lemma's hypothesis `|π_a| ≤ max(|π_Ω|, a)` needs. They are preserved along
   the families that occur (`ExpCond (ε + Ω^e·a') e` from `ExpCond ε (e+1)`).
2. **"Good" at type 2** is: good functions to good functions, and `B_0 K ≤ G K` pointwise. The second clause gives
   everything else that was needed (orbit `a ↦ G^a H` increasing, strict; fixed points of `a ↦ (G^a H) 0` are limits
   closed under the family, via `K(K 0) < B_0 K 0 ≤ G K 0`; `B_1 G` strictly above `G`). At type `k+1` the clause
   should read "after applying to good arguments down to type `A_1`, `Φ G h⃗ ≥ B_0 (G h⃗)` pointwise"; for `Φ = B_k`
   this is `korbit_le_diag` one type up.
3. **The proof of `B_k` has weight 1 is the same at every `k ≥ 1`**: orbit membership by induction on `a` (successor
   = hypothesis on `Φ`, limit = `stepLimit` after full application), then `stepDiagonal` on the fully applied
   family. The three norm hypotheses of `stepDiagonal`/`stepLimit` for the family `a ↦ Ω^(ε + η_a)` were derived
   from facts about the exponent family `η_a` by one pattern (`log_split` + `norm_ge_log` + `norm_opow`): this is
   the *family-lifting lemma* and should be stated once, abstractly: if `(η_a)` is cofinal-with-norm-bound and
   norm-monotone towards `η_Ω`, and `ExpCond`-style separation holds for `ε` below `η_Ω`, then so is
   `(Ω^(ε + η_a))` towards `Ω^(ε + η_Ω)`.
4. **Countability.** `opWeightSuccessor` is proved for countable weights `e` (it uses `norm_leading`,
   `norm_div_le`, `norm_ge_of_mul_le`, `nsep_step`, all for countable exponents). Level 3 needs it for weights
   `s < Ω^Ω`; the generalization replaces those four by their `norm_leading_gen` versions and is mechanical.

Proposed uniform objects (to freeze next, after (4)):

- `Good k : Value (tier (k+1)) → Prop` by recursion on `k` (`Good 0 = GoodFn`;
  `Good (k+1) Φ := ∀ G, Good k G → Good k (Φ G) ∧ Dom k G (Φ G)`), with `Dom` the applied-down domination of item 2.
- `Weight k : Ordinal → Value (tier (k+1)) → Prop` (`Weight 0 ε H := IsStep ε H`;
  `Weight (k+1) s Φ := Good (k+1) Φ ∧ ∀ ε G, ExpCond ε s → Weight k ε G → Weight k (ε + Ω^s) (Φ G)`).
- Theorem (W): `∀ k s Φ, Weight (k+1) s Φ → Weight (k+1) (s+1) (towerValue fix (k+1) Φ)` and the base
  `Weight 1 0 (towerValue fix 0)`; corollary `Weight l e (B_{l-1}^e B_{l-2})`, hence `PsiTowerLevelAt l` by the
  empty-context argument of `psiO_tower_two` (which is level-independent once `Weight` and the restart lemma are
  available) and `LevelFactsAt l` from `Good`.

The Lean risk is the recursion over `Value (tier k)` and the "apply down to type `A_1`" bookkeeping (root's
`semDown`/`spineValue` already do this for the diagonal); the mathematics has no new ingredient beyond what is
gated.
