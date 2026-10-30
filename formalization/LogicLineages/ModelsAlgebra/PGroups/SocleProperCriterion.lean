module
public import LogicLineages.ModelsAlgebra.PGroups.SocleProperCriterionTargets
public import LogicLineages.ModelsAlgebra.PGroups.SocleCorrectionCriterion
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
universe u v

theorem socle_proper_criterion : Targets.groupSocleProperCriterion.{u,v} := by
  intro G _ p B α
  rw [socle_correction_nonsurjective]
  constructor
  · rintro ⟨a,ha,havoid⟩
    have hanext : (a:G) ∉ (transfiniteFiltration p (α+1) : AddSubgroup G) := by
      rwa [transfiniteFiltration_add_one]
    have haB : (a:G) ∉ B := by
      intro hab
      have hn := havoid ⟨-(a:G),B.neg_mem hab⟩
      apply hn
      simpa only [add_neg_cancel] using (pStep p (transfiniteFiltration p α : AddSubgroup G)).zero_mem
    refine ⟨a,a.property,hanext,haB,?_⟩
    intro b β hab
    by_cases hβα : β ≤ α
    · exact transfiniteFiltration_antitone p hβα a.property.1
    · have hαβ : α+1 ≤ β := Order.succ_le_of_lt (lt_of_not_ge hβα)
      have hm := transfiniteFiltration_antitone p hαβ hab
      change (a:G)+b ∈ (transfiniteFiltration p (α+1) : AddSubgroup G) at hm
      rw [transfiniteFiltration_add_one] at hm
      exact False.elim (havoid b hm)
  · rintro ⟨a,ha,hanext,haB,hproper⟩
    refine ⟨⟨a,ha⟩,?_,?_⟩
    · rwa [transfiniteFiltration_add_one] at hanext
    · intro b hab
      apply hanext
      apply hproper b (α+1)
      rwa [transfiniteFiltration_add_one]

end LogicLineages.ModelsAlgebra.PGroups
