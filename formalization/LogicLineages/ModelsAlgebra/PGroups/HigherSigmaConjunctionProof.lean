module
public import LogicLineages.ModelsAlgebra.PGroups.HigherSigmaConjunctionTargets
public import LogicLineages.ModelsAlgebra.PGroups.SigmaTwoConjunction
public import LogicLineages.ModelsAlgebra.PGroups.RawHierarchyProof
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
open GroupInfinitary

theorem higher_sigma_conjunction_complexity : Targets.higherSigmaConjunctionComplexity := by
  intro α htwo n φ ψ hφ hψ
  cases hφ with
  | qf side q => exact (not_le_of_gt (show (0:Ordinal.{0})<2 from zero_lt_two) htwo).elim
  | sigma hpos s m matrix β lower rank =>
    cases hψ with
    | qf side q => exact (not_le_of_gt (show (0:Ordinal.{0})<2 from zero_lt_two) htwo).elim
    | sigma hpos' t l other γ lower' rank' =>
      let ρ : s×t→Ordinal.{0} := fun k=>max 1 (max (β k.1) (γ k.2))
      unfold sigmaTwoConjunction
      apply countable_disj_ex_complexity α hpos (s×t) n
        (fun k=>m k.1+l k.2)
        (fun k=>piConjunction
          (piOneNormalize (renameFormula (joinLeft n (m k.1) (l k.2)) (matrix k.1)))
          (piOneNormalize (renameFormula (joinRight n (m k.1) (l k.2)) (other k.2)))) ρ
      · intro k
        exact max_lt_iff.mpr ⟨lt_of_lt_of_le one_lt_two htwo,
          max_lt_iff.mpr ⟨lower k.1,lower' k.2⟩⟩
      · intro k
        have hρ : ρ k≠0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
        have hβ : β k.1≤ρ k := (le_max_left _ _).trans (le_max_right _ _)
        have hγ : γ k.2≤ρ k := (le_max_right _ _).trans (le_max_right _ _)
        apply pi_conjunction_complexity (ρ k) hρ _ _ _
        · exact (raw_pi_normalization (β k.1) (ρ k) hρ hβ _ _
            (infinitary_renaming_complexity .pi (β k.1) _ _
              (joinLeft n (m k.1) (l k.2)) (matrix k.1) (rank k.1))).1
        · exact (raw_pi_normalization (γ k.2) (ρ k) hρ hγ _ _
            (infinitary_renaming_complexity .pi (γ k.2) _ _
              (joinRight n (m k.1) (l k.2)) (other k.2) (rank' k.2))).1

end LogicLineages.ModelsAlgebra.PGroups
