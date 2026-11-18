module
public import LogicLineages.CartierObserverCurrent.RepeatedCartierTargets
public import LogicLineages.CartierObserverCurrent.LocalPolynomialProof
public meta import LogicLineages.Audit

@[expose] public section
universe u
namespace LogicLineages.CartierObserverCurrent.RepeatedCartier
open Basic SplittingRoots

private theorem cartier_zero (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2] :
    actualDifferentialCartier (0 : RatFunc K) = 0 := by
  simpa using actualDifferentialCartierCharacterization K 0 0

private theorem iterate_zero (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2]
    (ell : Nat) : (actualDifferentialCartier (K := K))^[ell] 0 = 0 := by
  induction ell with
  | zero => rfl
  | succ ell ih => rw [Function.iterate_succ_apply, cartier_zero, ih]

theorem simpleIteration : Targets.SimpleIteration.{u} := by
  intro K _ _ _ z b ell
  induction ell generalizing b with
  | zero => rfl
  | succ ell ih =>
    rw [Function.iterate_succ_apply]
    have h := ((LocalPolynomial.localPolePolynomialRule K).1 z b 0).2
    simp only [Nat.mul_zero, Nat.zero_add, pow_one] at h
    rw [h, ih, Function.iterate_succ_apply]

theorem higherVanishing : Targets.HigherVanishing.{u} := by
  intro K _ _ _ z b ell
  induction ell generalizing b with
  | zero => intro k hk hle; simp only [pow_zero] at hle; omega
  | succ ell ih =>
    intro k hk hle
    rw [Function.iterate_succ_apply]
    have hcases : k = 2 * (k / 2) ∨ k = 2 * (k / 2) + 1 := by omega
    rcases hcases with he | ho
    · have h := ((LocalPolynomial.localPolePolynomialRule K).1 z b (k / 2)).1
      rw [← he] at h
      rw [h, iterate_zero]
    · have h := ((LocalPolynomial.localPolePolynomialRule K).1 z b (k / 2)).2
      rw [← ho] at h
      rw [h]
      apply ih
      · omega
      · rw [pow_succ] at hle
        omega

private theorem cartier_sum (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2]
    {ι : Type*} (s : Finset ι) (f : ι → RatFunc K) :
    actualDifferentialCartier (∑ z ∈ s, f z) = ∑ z ∈ s, actualDifferentialCartier (f z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, cartier_zero]
  | @insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, cartierAdd, ih]

private theorem iterate_sum (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2]
    {ι : Type*} (s : Finset ι) (f : ι → RatFunc K) (ell : Nat) :
    (actualDifferentialCartier (K := K))^[ell] (∑ z ∈ s, f z) =
      ∑ z ∈ s, (actualDifferentialCartier (K := K))^[ell] (f z) := by
  induction ell generalizing f with
  | zero => rfl
  | succ ell ih =>
    rw [Function.iterate_succ_apply, cartier_sum, ih]
    apply Finset.sum_congr rfl
    intro z _
    rw [Function.iterate_succ_apply]

theorem finiteAdditivity : Targets.FiniteAdditivity.{u} := by
  intro K _ _ _ n ell f
  exact iterate_sum K Finset.univ f ell

theorem principalReduction : Targets.PrincipalReduction := by
  intro d M hM b ell hbound
  classical
  letI : Fintype (Root d) := by unfold Root; infer_instance
  unfold InitialPrincipalParts.reconstruct RationalCoverage.reconstruct
  rw [iterate_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [iterate_sum, Finset.sum_eq_single (⟨0, hM⟩ : Fin M)]
  · simpa only [Nat.zero_add, pow_one] using simpleIteration (FieldAt d) z.val (b z ⟨0, hM⟩) ell
  · intro j _ hj
    apply higherVanishing (FieldAt d) z.val (b z j) ell (j.val + 1)
    · have hn : j.val ≠ 0 := by intro h; apply hj; exact Fin.ext h
      omega
    · exact (Nat.succ_le_of_lt j.isLt).trans hbound
  · simp

#audit_namespace LogicLineages.CartierObserverCurrent.RepeatedCartier
end LogicLineages.CartierObserverCurrent.RepeatedCartier
