module

public import LogicLineages.ModelsAlgebra.PGroups.SigmaTwoConjunctionTargets
public import LogicLineages.ModelsAlgebra.PGroups.PiConjunction
public import LogicLineages.ModelsAlgebra.PGroups.InfinitaryRenaming

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

open GroupBackAndForth
universe u v

theorem join_left_assignment : Targets.groupJoinLeftAssignment.{u} := by
  intro G n m l a w
  funext i
  induction i using Fin.addCases <;> simp [joinLeft, append]

theorem join_right_assignment : Targets.groupJoinRightAssignment.{u} := by
  intro G n m l a w
  funext i
  induction i using Fin.addCases <;> simp [joinRight, append]

theorem sigma_two_conjunction_realization : Targets.groupSigmaTwoConjunctionRealization.{u} := by
  intro G _ n φ ψ a
  cases φ with
  | qf q =>
    cases ψ <;> exact ordinary_conjunction_realization G _ _ a
  | conjAll s m matrix =>
    cases ψ <;> exact ordinary_conjunction_realization G _ _ a
  | disjEx s m matrix =>
    cases ψ with
    | qf q => exact ordinary_conjunction_realization G _ _ a
    | conjAll t l other => exact ordinary_conjunction_realization G _ _ a
    | disjEx t l other =>
      unfold sigmaTwoConjunction
      rw [countable_disj_ex_realization (s × t) n _ _ G a]
      simp only [pi_conjunction_realization G, pi_one_normalization_realization G,
        infinitary_renaming_realization G, join_left_assignment G, join_right_assignment G,
        Formula.Realize]
      constructor
      · rintro ⟨⟨i, j⟩, w, hl, hr⟩
        exact ⟨⟨i, (fun k => w (Fin.castAdd (l j) k)), hl⟩,
          ⟨j, (fun k => w (Fin.natAdd (m i) k)), hr⟩⟩
      · rintro ⟨⟨i, d, hd⟩, ⟨j, e, he⟩⟩
        refine ⟨(i, j), append d e, ?_, ?_⟩
        · simpa only [append, Fin.addCases_left] using hd
        · simpa only [append, Fin.addCases_right] using he

theorem sigma_two_conjunction_complexity : Targets.groupSigmaTwoConjunctionComplexity.{v} := by
  intro n φ ψ hφ hψ
  generalize hα : (2 : Ordinal.{v}) = α at hφ hψ
  cases hφ with
  | qf side q => simp at hα
  | sigma positive s m matrix β lower rank =>
    cases hψ with
    | qf side q => simp at hα
    | sigma positive' t l other γ lower' rank' =>
      subst α
      apply countable_disj_ex_complexity (2 : Ordinal.{v}) (by simp) (s × t) n
        (fun k => m k.1 + l k.2)
        (fun k => piConjunction
          (piOneNormalize (renameFormula (joinLeft n (m k.1) (l k.2)) (matrix k.1)))
          (piOneNormalize (renameFormula (joinRight n (m k.1) (l k.2)) (other k.2))))
        (fun _ => 1)
      · intro k
        exact one_lt_two
      · intro k
        apply pi_conjunction_complexity (1 : Ordinal.{v}) one_ne_zero _ _ _
        · apply pi_one_normalization_complexity (β k.1)
            (lower k.1) _ _
          exact infinitary_renaming_complexity .pi (β k.1) _ _
            (joinLeft n (m k.1) (l k.2)) (matrix k.1) (rank k.1)
        · apply pi_one_normalization_complexity (γ k.2)
            (lower' k.2) _ _
          exact infinitary_renaming_complexity .pi (γ k.2) _ _
            (joinRight n (m k.1) (l k.2)) (other k.2) (rank' k.2)

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
