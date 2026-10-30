module
public import LogicLineages.ModelsAlgebra.PGroups.SocleGapRootTargets
public import LogicLineages.ModelsAlgebra.PGroups.ProperSocleTransport
public import LogicLineages.ModelsAlgebra.PGroups.HigherPerturbation
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
universe u v

theorem socle_gap_suitable_root : Targets.groupSocleGapSuitableRoot.{u,v} := by
  intro G H _ _ p _ B C _ x α hxB hpx f hpres hRank hx hxnot hgap hproper
  have hroot := hgap
  rw [transfiniteFiltration_add_one] at hroot
  obtain ⟨z,hz,hpz⟩ := hroot
  change p • z = p • x at hpz
  obtain ⟨ha,hanext,haB,haprop⟩ := higher_perturbation_proper G p B x (-z) α hx hxnot hproper
    ((transfiniteFiltration p (α+1) : AddSubgroup G).neg_mem hz)
  have hasocle : x + -z ∈ pSocle p (transfiniteFiltration p α) := by
    refine ⟨ha,?_⟩
    change p • (x + -z) = 0
    rw [smul_add,smul_neg,hpz,add_neg_cancel]
  obtain ⟨w1,hw1,hw1not,hw1C,hw1proper⟩ :=
    proper_socle_transport G H p B C f α hpres hRank (x + -z) hasocle hanext haB haprop
  let px : B := ⟨p • x,hpx⟩
  have htarget : (f px:H) ∈ (transfiniteFiltration p (α+1+1) : AddSubgroup H) :=
    (hpres px (α+1+1) le_rfl).mpr hgap
  rw [transfiniteFiltration_add_one] at htarget
  obtain ⟨w2,hw2,hpw2⟩ := htarget
  change p • w2 = (f px:H) at hpw2
  have hnew := higher_perturbation_proper H p C w1 w2 α hw1.1 hw1not hw1proper hw2
  refine ⟨w1+w2,?_,hnew⟩
  have hpw1 : p • w1 = 0 := hw1.2
  rw [smul_add,hpw1,zero_add,hpw2]

end LogicLineages.ModelsAlgebra.PGroups
