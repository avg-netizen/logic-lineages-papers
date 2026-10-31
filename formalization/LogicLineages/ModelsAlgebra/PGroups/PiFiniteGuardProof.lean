module
public import LogicLineages.ModelsAlgebra.PGroups.PiFiniteGuardTargets
public import LogicLineages.ModelsAlgebra.PGroups.PiConjunction
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
open GroupInfinitary
universe u

private theorem pi_join_realize (G : Type u) [AddCommGroup G] (n : ℕ)
    (φ ψ : Formula n) (a : Fin n → G) :
    (piJoin φ ψ).Realize a ↔ φ.Realize a ∧ ψ.Realize a := by
  cases φ <;> cases ψ <;> dsimp only [piJoin]
  all_goals first | exact Iff.rfl | exact pi_conjunction_realization G n _ _ a

private theorem pi_join_complexity (α : Ordinal.{0}) (n : ℕ) (φ ψ : Formula n)
    (hφ : Complexity .pi α φ) (hψ : Complexity .pi α ψ) :
    Complexity .pi α (piJoin φ ψ) := by
  cases hφ with
  | qf side p =>
    cases hψ with
    | qf side q => exact Complexity.qf .pi (.and p q)
    | pi hα s m matrix β lower rank => exact (hα rfl).elim
  | pi hα s m matrix β lower rank =>
    cases hψ with
    | qf side q => exact (hα rfl).elim
    | pi hα' s' m' matrix' β' lower' rank' =>
      exact pi_conjunction_complexity α hα n _ _
        (Complexity.pi hα s m matrix β lower rank)
        (Complexity.pi hα' s' m' matrix' β' lower' rank')

theorem pi_finite_guard_exact : Targets.piFiniteGuardExact.{u} := by
  intro α n fs
  induction fs with
  | nil =>
    intro _
    by_cases hα : α=0
    · subst α
      refine ⟨by simpa [piFiniteGuard,piTruth] using
        Complexity.qf .pi (QF.equal (.zero : GroupBackAndForth.GroupTerm n) .zero),?_⟩
      intro G _ a
      simp [piFiniteGuard,piTruth,Formula.Realize,QF.Realize]
    · refine ⟨by simpa only [piFiniteGuard,piTruth,if_neg hα] using
        (pi_qf_padding.{u,0} α hα n (.equal .zero .zero)).1,?_⟩
      intro G _ a
      simp only [piFiniteGuard,piTruth,if_neg hα]
      rw [(pi_qf_padding.{u,0} α hα n (.equal .zero .zero)).2 G a]
      simp [QF.Realize]
  | cons φ fs ih =>
    intro hs
    have hφ := hs φ (by simp)
    have htail : ∀ ψ ∈ fs, Complexity .pi α ψ := fun ψ hψ => hs ψ (by simp [hψ])
    obtain ⟨hc,hr⟩ := ih htail
    refine ⟨pi_join_complexity α n φ (piFiniteGuard α fs) hφ hc,?_⟩
    intro G _ a
    have hh := (pi_join_realize G n φ (piFiniteGuard α fs) a).trans (and_congr Iff.rfl (hr G a))
    simpa only [piFiniteGuard,List.forall_mem_cons] using hh

theorem pi_successor_padding : Targets.piSuccessorPadding.{u} := by
  intro α n φ h
  refine ⟨?_,fun G _ a => pi_one_normalization_realization G n φ a⟩
  cases h with
  | qf side q =>
    simpa only [zero_add,piOneNormalize] using (pi_qf_padding.{u,0} 1 one_ne_zero n q).1
  | pi hα s m matrix β lower rank =>
    exact positive_complexity_monotone .pi α (α+1) n (.conjAll s m matrix) hα
      (Order.le_succ α) (Complexity.pi hα s m matrix β lower rank)
end LogicLineages.ModelsAlgebra.PGroups
