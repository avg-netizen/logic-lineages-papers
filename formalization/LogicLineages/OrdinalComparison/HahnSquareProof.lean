module
public import LogicLineages.OrdinalComparison.HahnSquareTargets
public import Lean.Elab.Tactic.Omega

@[expose] public section
universe u
namespace LogicLineages.OrdinalComparison

private theorem off_diagonal_sum {K : Type*} [Field K] [CharP K 2]
    (F : HahnSeries Int K) (S : Finset (Int × Int))
    (hs : ∀ p ∈ S, p.swap ∈ S) (hd : ∀ p ∈ S, p.1 ≠ p.2) :
    (∑ p ∈ S, F.coeff p.1 * F.coeff p.2) = 0 := by
  classical
  apply Finset.sum_involution (fun p _ => p.swap)
  · intro p hp
    dsimp
    rw [mul_comm (F.coeff p.2) (F.coeff p.1), CharTwo.add_self_eq_zero]
  · intro p hp hval heq
    have he := congrArg Prod.fst heq
    exact hd p hp he.symm
  · intro p hp
    exact Prod.swap_swap p
  · exact hs

theorem actualHahnSquareEvenCoefficient : Targets.ActualHahnSquareEvenCoefficient.{u} := by
  intro K _ _ F n
  classical
  let S := Finset.addAntidiagonal F.isPWO_support F.isPWO_support (2 * n)
  have hz : (∑ p ∈ S.erase (n, n), F.coeff p.1 * F.coeff p.2) = 0 := by
    apply off_diagonal_sum
    · intro p hp
      obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hp
      apply Finset.mem_erase.mpr
      refine ⟨?_, Finset.swap_mem_addAntidiagonal.mpr hmem⟩
      intro he
      apply hne
      simpa using congrArg Prod.swap he
    · intro p hp he
      obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hp
      have hsum := (Finset.mem_addAntidiagonal.mp hmem).2.2
      apply hne
      apply Prod.ext <;> dsimp at * <;> omega
  rw [pow_two, HahnSeries.coeff_mul]
  change (∑ p ∈ S, F.coeff p.1 * F.coeff p.2) = _
  by_cases hn : F.coeff n = 0
  · have hnot : (n, n) ∉ S := by simp [S, Finset.mem_addAntidiagonal, HahnSeries.mem_support, hn]
    rw [Finset.erase_eq_of_notMem hnot] at hz
    simpa [hn] using hz
  · have hmem : (n, n) ∈ S := by
      simp [S, Finset.mem_addAntidiagonal, HahnSeries.mem_support, hn, two_mul]
    rw [← Finset.sum_erase_add _ _ hmem, hz, zero_add, pow_two]

theorem actualHahnSquareOddCoefficient : Targets.ActualHahnSquareOddCoefficient.{u} := by
  intro K _ _ F n
  rw [pow_two, HahnSeries.coeff_mul]
  apply off_diagonal_sum
  · intro p hp
    exact Finset.swap_mem_addAntidiagonal.mpr hp
  · intro p hp he
    have hsum := (Finset.mem_addAntidiagonal.mp hp).2.2
    omega

end LogicLineages.OrdinalComparison
