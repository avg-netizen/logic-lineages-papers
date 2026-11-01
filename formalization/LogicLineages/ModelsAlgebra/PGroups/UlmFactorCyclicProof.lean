module
public import LogicLineages.ModelsAlgebra.PGroups.UlmFactorCyclicTargets
public import LogicLineages.ModelsAlgebra.PGroups.InitialUlmFactorProof
public import LogicLineages.ModelsAlgebra.PGroups.ZeroOmegaCyclicProof
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

theorem actual_ulm_factor_cyclic_presentation : Targets.actualUlmFactorCyclicPresentation := by
  intro p _ G _ _ hG ξ
  let S:AddSubgroup G:=transfiniteFiltration p (Ordinal.omega0*ξ)
  let U:AddSubgroup S:=transfiniteFiltration p (Ordinal.omega0:Ordinal.{0})
  let C:=UlmFactor p G ξ
  letI:Countable C:=(QuotientAddGroup.mk'_surjective U).countable
  have hS:∀x:S,∃k:ℕ,p^k • x=0:=by
    intro x
    obtain ⟨k,hk⟩:=hG (x:G)
    exact ⟨k,Subtype.ext hk⟩
  obtain ⟨I,hI,he,_⟩:=countable_zero_omega_cyclic_decomposition p C
    (p_primary_quotient S p U hS) (ulm_factor_omega_zero G p ξ)
  exact ⟨I,hI,he⟩

theorem reduced_ulm_factor_nontrivial : Targets.reducedUlmFactorNontrivial := by
  classical
  intro p _ G _ _ hG hr ξ hNZ
  let cut:=Ordinal.omega0*ξ
  let S:AddSubgroup G:=transfiniteFiltration p cut
  let U:AddSubgroup S:=transfiniteFiltration p (Ordinal.omega0:Ordinal.{0})
  let C:=UlmFactor p G ξ
  let q:=QuotientAddGroup.mk' U
  by_contra hnontriv
  have hzero:∀x:C,x=0:=by
    intro x
    by_contra hx
    exact hnontriv ⟨⟨x,0,hx⟩⟩
  have htop:(⊤:AddSubgroup S)≤U:=by
    intro x _
    exact (QuotientAddGroup.eq_zero_iff _).mp (hzero (q x))
  have hs:StableAt p S 0:=by
    rw [StableAt,transfiniteFiltration_zero,zero_add]
    apply le_antisymm _ le_top
    exact htop.trans (transfiniteFiltration_antitone p Ordinal.one_lt_omega0.le)
  have hg:StableAt p G cut:=by
    have he:=congrArg (fun A:AddSubgroup S=>A.map S.subtype) hs
    rw [transfinite_tail_image,transfinite_tail_image] at he
    simpa only [StableAt,add_zero,zero_add] using he
  exact hNZ (hr _ (primary_stable_stage G p hG cut hg).1)
end LogicLineages.ModelsAlgebra.PGroups
