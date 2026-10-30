module
public import LogicLineages.ModelsAlgebra.PGroups.HigherPerturbationTargets
public import Mathlib.Tactic.Abel
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
universe u v

theorem higher_perturbation_proper : Targets.groupHigherPerturbationProper.{u,v} := by
  intro G _ p B x z α hx hxnot hproper hz
  have hnew : x+z ∈ (transfiniteFiltration p α : AddSubgroup G) :=
    (transfiniteFiltration p α).add_mem hx (transfiniteFiltration_antitone p le_self_add hz)
  have hbad (b : B) : (x+z)+b ∉ (transfiniteFiltration p (α+1) : AddSubgroup G) := by
    intro h
    have hm := (transfiniteFiltration p (α+1) : AddSubgroup G).sub_mem h hz
    have he : (x+z+(b:G))-z = x+(b:G) := by abel
    rw [he] at hm
    exact hxnot (hproper b (α+1) hm)
  have hnot : x+z ∉ (transfiniteFiltration p (α+1) : AddSubgroup G) := by
    simpa only [AddSubgroup.coe_zero,add_zero] using hbad 0
  have hout : x+z ∉ B := by
    intro hb
    apply hbad ⟨-(x+z),B.neg_mem hb⟩
    simpa only [add_neg_cancel] using (transfiniteFiltration p (α+1) : AddSubgroup G).zero_mem
  refine ⟨hnew,hnot,hout,?_⟩
  intro b β hb
  by_cases hβα : β ≤ α
  · exact transfiniteFiltration_antitone p hβα hnew
  · have hab : α+1 ≤ β := Order.succ_le_of_lt (lt_of_not_ge hβα)
    exact False.elim (hbad b (transfiniteFiltration_antitone p hab hb))

end LogicLineages.ModelsAlgebra.PGroups
