module

public import LogicLineages.ModelsAlgebra.PGroups.BoundedUlmTableTargets
public import LogicLineages.ModelsAlgebra.PGroups.InfiniteUlm
public import LogicLineages.ModelsAlgebra.PGroups.FiniteConjunction
public import LogicLineages.ModelsAlgebra.PGroups.InfinitaryWrap
public import LogicLineages.ModelsAlgebra.PGroups.Annihilation

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
universe u v

theorem positive_pi_all_complexity : Targets.groupPositivePiAllComplexity.{v} := by
  intro α hα n fs
  induction fs with
  | nil =>
    intro h
    exact (pi_qf_padding.{0,v} α hα n (.neg .falsum)).1
  | cons φ fs ih =>
    intro h
    exact pi_conjunction_complexity α hα n φ (piTwoAll fs)
      (h φ List.mem_cons_self) (ih (fun ψ hψ => h ψ (List.mem_cons_of_mem _ hψ)))

theorem ulm_rank_entry : Targets.groupUlmRankEntry.{u,v} := by
  intro p _ j n entry
  cases entry with
  | none =>
    exact ⟨(infinite_ulm_formula.{u,v} p j n).1,
      fun G _ _ a => countable_infinite_ulm_formula p G j n a⟩
  | some m =>
    constructor
    · change Complexity .pi (3 : Ordinal.{v})
        (piConjunction (piWrap (ulmLowerFormula p j n m)) (ulmUpperFormula p j n m))
      apply pi_conjunction_complexity 3 (by simp)
      · exact pi_wrap_complexity 3 2 (by simp)
          (by exact_mod_cast (show (2 : ℕ) < 3 from by decide)) n _
          (ulm_lower_formula.{0,v} p j n m).1
      · exact positive_complexity_monotone .pi 2 3 n _ (by simp)
          (by exact_mod_cast (show (2 : ℕ) ≤ 3 from by decide))
          (ulm_upper_rank_formula.{0,v} p j n m).1
    · intro G _ _ a
      change (piConjunction (piWrap (ulmLowerFormula p j n m)) (ulmUpperFormula p j n m)).Realize a ↔ _
      rw [pi_conjunction_realization G n, pi_wrap_realization G n,
        ulm_lower_rank_formula p j n m G a, (ulm_upper_rank_formula.{u,0} p j n m).2 G a]
      exact ⟨fun h => le_antisymm h.2 h.1, fun h => ⟨h.ge, h.le⟩⟩

theorem bounded_ulm_table : Targets.groupBoundedUlmTable.{u,v} := by
  intro p _ N entries
  constructor
  · apply positive_pi_all_complexity 3 (by simp)
    intro φ hφ
    simp only [List.mem_cons, List.mem_ofFn] at hφ
    rcases hφ with rfl | ⟨i, rfl⟩
    · exact positive_complexity_monotone .pi 1 3 0 _ (by simp)
        (by exact_mod_cast (show (1 : ℕ) ≤ 3 from by decide))
        (annihilation_formula.{0,v} (p ^ N) 0).1
    · exact (ulm_rank_entry.{0,v} p i.val 0 (entries i)).1
  · intro G _ _
    unfold boundedUlmTable
    rw [pi_two_all_realization G 0]
    simp only [List.forall_mem_cons, List.forall_mem_ofFn_iff]
    rw [finite_exponent_formula G p N 0]
    simp only [(ulm_rank_entry.{u,0} p _ 0 _).2 G]

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
