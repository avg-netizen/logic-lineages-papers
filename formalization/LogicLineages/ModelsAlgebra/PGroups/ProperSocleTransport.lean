module
public import LogicLineages.ModelsAlgebra.PGroups.ProperSocleTransportTargets
public import LogicLineages.ModelsAlgebra.PGroups.SocleCorrectionStrictRank
public import LogicLineages.ModelsAlgebra.PGroups.SocleCorrectionTransport
public import LogicLineages.ModelsAlgebra.PGroups.SocleProperCriterion
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
universe u v

theorem proper_socle_transport : Targets.groupProperSocleTransport.{u,v} := by
  intro G H _ _ p _ B C _ f α hpres hRank a ha hanext haB hproper
  letI : Finite C := Finite.of_injective f.symm f.symm.injective
  have hs (b : B) : (f b:H) ∈ (transfiniteFiltration p α : AddSubgroup H) ↔
      (b:G) ∈ (transfiniteFiltration p α : AddSubgroup G) :=
    hpres b α ((le_self_add : α ≤ α+1).trans le_self_add)
  have h1 (b : B) : (f b:H) ∈ pStep p (transfiniteFiltration p α : AddSubgroup H) ↔
      (b:G) ∈ pStep p (transfiniteFiltration p α : AddSubgroup G) := by
    simpa only [transfiniteFiltration_add_one] using hpres b (α+1) le_self_add
  have h2 (b : B) : (f b:H) ∈ pStep p (pStep p (transfiniteFiltration p α : AddSubgroup H)) ↔
      (b:G) ∈ pStep p (pStep p (transfiniteFiltration p α : AddSubgroup G)) := by
    simpa only [transfiniteFiltration_add_one] using hpres b (α+1+1) le_rfl
  have hn := (socle_proper_criterion G p B α).mpr ⟨a,ha,hanext,haB,hproper⟩
  have hr := (socle_correction_strict_rank G p B (transfiniteFiltration p α)).mp hn
  have he := socle_correction_rank_transport G H p B (transfiniteFiltration p α)
    C (transfiniteFiltration p α) f hs h1 h2
  have hrt : Module.rank (ZMod p) (SocleCorrectionQuotient H p C (transfiniteFiltration p α)) <
      Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α : AddSubgroup H)) := by
    rw [← he]
    exact hr.trans_le hRank
  exact (socle_proper_criterion H p C α).mp
    ((socle_correction_strict_rank H p C (transfiniteFiltration p α)).mpr hrt)

end LogicLineages.ModelsAlgebra.PGroups
