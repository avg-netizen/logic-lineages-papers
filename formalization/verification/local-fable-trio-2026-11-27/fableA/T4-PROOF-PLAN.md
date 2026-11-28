# T4 proof plan (Fable A, 27 November 2026)

Target: `ActualCalibrationThree.PsiPowerLevel` (frozen, unchanged): for countable `e ≥ 1` with no fixed
point of `L := (β ↦ D β 0)` in `[1, e]`, `ψ(Ω^e) = L e`. Verdict: true as frozen; hypothesis necessary
(with `L λ = λ`, `1 ≤ λ < e`, the clause (P) stalls and `ψ(Ω^e) = λ`).

Notation. `N = N_B`, `Γ = Γ_0`, `F α = N^α(Γ)` (criticals = range of `F`), `D β = B_0^β(N)` (`level`),
`E_β(α) = (D β)^α(0)` (`levelEnum`), `|·|` the coefficient norm, `Ω = ω₁`, `Top = Ω^Ω = a_3`.
`ψ` is extended to all ordinals by `psiO ξ = ψ ξ` for `ξ ≤ Λ` (junk 0 above); everything below stays `≤ Top`.

## 0. What the round-6 note got right and what changes

- Right: two-sided argument, upper bound by leastness in (P), lower bound by closure.
- Changed: no explicit formula `ψ(Ω^e·a + ρ) = …` and no Cantor-normal-form recursion `κ_l` is needed.
  The induction-loading statements are two *one-step* inequalities about an arbitrary context `ζ`
  (the part of the index to the left), each proved by induction on `e`; the context is abstract and only
  has to satisfy a norm-separation property. The "collapse phenomenon" is handled by one generic lemma
  (stall) instead of being described.

## 1. Generic facts about the (P)-collapse (any index `≤ Λ`)

- C1 `psiO_mono`: `ξ ≤ ξ'` ⟹ `ψ ξ ≤ ψ ξ'`. (Leastness at `ξ` with candidate `ψ ξ'`.)
- C2 `psiO_stall`: if `ζ ≤ ξ` and every `η ∈ [ζ, ξ)` has `|η| ≥ ψ ζ`, then `ψ ξ = ψ ζ`.
  (Leastness at `ξ` with candidate `ψ ζ`: an `η < ξ` with `|η| < ψ ζ` lies below `ζ`.)
- C4 `crit_step`: criticals `x < θ` ⟹ `N x ≤ θ`.
- `critLim`: a countable `θ > 0` such that every `y < θ` has a critical `c` with `y < c ≤ θ` is critical.

## 2. Function side (no ψ)

- H3 `veblen_double`: `y + y ≤ N y`. Route: `g α := (B_0^α Next) 0`; `N = fix g`; `N y ≥ g(y+1)`
  (`fix_ge_stage_one`); `g(y+1) = B_0 H 0 ≥ H(H 0)` for `H = B_0^y Next` (stage two of `fix`);
  `H c ≥ Next c ≥ ω^{c+1} ≥ c + c`; `g y ≥ y` by induction.
- H4 for a positive fixed point `κ` of `E_β`: `ω < κ`; `κ` is a limit; `y < κ ⟹ D β y < κ`;
  `y, b < κ ⟹ y + b < κ`; `y, b < κ ⟹ (D β)^b(y) < κ` (start-monotonicity + composition, `(D β)^b(y) ≤ E_β(y+b)`).
- H8 `level_lt_succ`: `D β x < D (β+1) x`.
- H7 `level_critical`: `D e x` is critical for `e ≥ 1` (induction on `e` with `critLim`; `e = 1` uses the
  n = 2 orbit comparison `F a ≤ N^{(ω+1)+a}(0)`).
- H9 `level_base_eq`: `D e Γ = D e 0` for `e ≥ 1` (from `Γ < D 1 0` and "`y < D e 0 ⟹ D e y ≤ D e 0`").
- L-facts: `L` strictly increasing, `α ≤ L α`, continuous at limits; closure ⟹ fixed point
  (`levelZero_closed_fix`).

## 3. Norm side

- B1 `norm_leading`: for `e < Ω`, `1 ≤ c < Ω`, `τ < Ω^e`: `|Ω^e·c + τ| = max(max(c, e), |τ|)`
  (`CNF.opow_mul_add`, `entry_le`, `norm_countable`).
- NF1 `norm_div_le`: `τ < Ω^{e+1}` ⟹ `∃ b < Ω, b ≤ |τ| ∧ τ < Ω^e·(b+1)`.
- NF2 `norm_ge_of_mul_le`: `1 ≤ b`, `Ω^e·b ≤ τ < Ω^{e+1}` ⟹ `max(b, e) ≤ |τ|`.
- NF3 `norm_ge_exponent`: `Ω^{e'} ≤ τ < Ω^e`, `e < Ω` ⟹ `e' ≤ |τ|`.
- Context predicate `NormSeparated ζ e :⟺ ∀ τ < Ω^e, |ζ + τ| = max(|ζ|, |τ|)`.
  `NormSeparated 0 e`; antitone in `e`; `NormSeparated ζ (e+1)`, `c < Ω` ⟹ `NormSeparated (ζ + Ω^e·c) e`
  and (`c ≠ 0`) `|ζ + Ω^e·c| = max(|ζ|, max(c, e))`.

## 4. The two induction-loading statements (frozen as `UpperStep`, `LowerStep`)

**UpperStep(e).** For all `ζ`, `x`: if `ζ + Ω^e ≤ Top`, `NormSeparated ζ e`, `x` critical and `ψ ζ ≤ x`,
then `ψ(ζ + Ω^e) ≤ D e x`.

Induction on `e`.
- `e = 0`: leastness at `ζ + 1` with the critical `N x`; every `η ≤ ζ` has `ψ η ≤ x < N x`.
- `e` limit: leastness with `D e x` (critical). For `η = ζ + τ`, `τ < Ω^e`: `τ < Ω^β` for some `β < e`, so
  `ψ η ≤ ψ(ζ + Ω^β) ≤ D β x < D (β+1) x ≤ D e x` (IH at `β`, H8).
- `e = e'+1`: `κ := D e x` is the least fixed point of `E_{e'}` above `x`. Chain (induction on `b`):
  `O(b) := (D e')^b(x)` is critical and `ψ(ζ + Ω^{e'}·b) ≤ O(b)` — successor by IH(`e'`) at the context
  `ζ + Ω^{e'}·b'` with value `O(b')`, limit by leastness with `O(b)` (no norm needed).
  Then for `η = ζ + τ < ζ + Ω^{e'+1}` with `|η| < κ`: NF1 gives `b ≤ |τ| ≤ |η| < κ` with
  `τ < Ω^{e'}(b+1)`, so `ψ η ≤ O(b+1) < κ` by H4.

**LowerStep(e).** For all `ζ`, `x`: if `ζ + Ω^e ≤ Top`, `NormSeparated ζ e`, `x ≤ ψ ζ`, and, with
`θ := ψ(ζ + Ω^e)`, both `|ζ| < θ` and `e < θ` ("the new index is active"), then `D e x ≤ θ`.

Induction on `e`.
- `e = 0`: closure gives `ψ ζ < θ`; C4 gives `N x ≤ N(ψ ζ) ≤ θ`.
- `e` limit: for `β < e`, the sub-index `ζ + Ω^β` is active: otherwise `ψ(ζ+Ω^β) ≤ max(|ζ|, β)`, every
  `η ∈ [ζ+Ω^β, ζ+Ω^e)` has `|η| ≥ max(|ζ|, β)` (NF3), so by stall `θ = ψ(ζ+Ω^β) ≤ max(|ζ|, β) < θ`.
  IH(`β`) gives `D β x ≤ ψ(ζ+Ω^β) ≤ θ`; take the supremum.
- `e = e'+1`: put `ξ_b := ζ + Ω^{e'}·b`. For `b < θ`: `|ξ_b| ≤ max(|ζ|, max(b, e')) < θ`, so `ψ ξ_b < θ`.
  Each `ξ_{b'+1}` with `b'+1 < θ` is active relative to `ξ_{b'}` (stall + NF2, same contradiction).
  Chain (induction on `b < θ`): `O(b) ≤ ψ ξ_b` — successor by IH(`e'`), limit by monotonicity of `ψ`.
  `θ` is a limit: if `θ = c+1` then `ψ ξ_c = c`, so `c` is critical and `c + c ≤ N c ≤ θ = c+1`, i.e.
  `c ≤ 1`, impossible for a critical. Hence `E_{e'}(θ) = sup_{b<θ} E_{e'}(b) ≤ θ`, `θ` is a fixed point of
  `E_{e'}` above `x`, and `D e x ≤ θ` by T3.

## 5. T4

Strong induction on `e`. Upper: `UpperStep(e)` at `ζ = 0`, `x = Γ = ψ 0`, then `D e Γ = D e 0` (H9).
Lower: `LowerStep(e)` at `ζ = 0`, `x = 0`; activity `e < ψ(Ω^e)`: otherwise `Θ := ψ(Ω^e) ≤ e`, and for
`1 ≤ e' < Θ` closure (`|Ω^{e'}| = e'`) and the induction hypothesis give `L e' < Θ`, so
`levelZero_closed_fix` yields a fixed point of `L` in `[1, Θ] ⊆ [1, e]`.

## 6. Module layering (each gated on its own)

1. `ActualCalibrationThreePsiTargets` — definitions `levelEnum`, `psiO`, `NormSeparated`; frozen statements.
2. `ActualCalibrationThreeHierarchyProof` — §2 except criticality.
3. `ActualCalibrationThreeCriticalProof` — C4, `critLim`, `level_critical`.
4. `ActualCalibrationThreeNormProof` — §3.
5. `ActualCalibrationThreePsiProof` — §1, `upperStep`, `lowerStep`.
6. `ActualCalibrationThreePowerProof` — `psiPowerLevel : PsiPowerLevel`.

T5 is root's (`PsiPowerLevel → CalibrationThree`).
