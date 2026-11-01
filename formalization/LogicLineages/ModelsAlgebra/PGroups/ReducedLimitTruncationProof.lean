module
public import LogicLineages.ModelsAlgebra.PGroups.ReducedLimitTruncationTargets
public import LogicLineages.ModelsAlgebra.PGroups.QuotientHeight
public import LogicLineages.ModelsAlgebra.PGroups.PPrimaryQuotient
public import LogicLineages.ModelsAlgebra.PGroups.StableStageProof
public import LogicLineages.ModelsAlgebra.PGroups.ZeroStageReduced
public import LogicLineages.ModelsAlgebra.PGroups.FiniteSocleReducedProof
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

theorem actual_reduced_limit_truncation : Targets.actualReducedLimitTruncation := by
  classical
  intro p _ G _ _ δ hδ hG hr hl
  let K:AddSubgroup G:=transfiniteFiltration p δ
  let Q:=G⧸K
  let q:=QuotientAddGroup.mk' K
  letI:Countable Q:=(QuotientAddGroup.mk'_surjective K).countable
  have hQ:=p_primary_quotient G p K hG
  have hz:(transfiniteFiltration p δ:AddSubgroup Q)=⊥:=by
    rw [quotient_filtration_below p K δ le_rfl δ le_rfl]
    apply le_antisymm _ bot_le
    rintro x ⟨y,hy,rfl⟩
    exact (QuotientAddGroup.eq_zero_iff _).mpr hy
  have hred:IsReducedAddGroup Q:=zero_stage_reduced Q p (Fact.out:p.Prime).ne_zero δ hz
  have hlong:StagesNonzeroBelow p Q δ:=by
    intro β hβ hzero
    have hs:(transfiniteFiltration p β:AddSubgroup G)≤K:=by
      intro x hx
      apply (QuotientAddGroup.eq_zero_iff _).mp
      change q x=0
      have hh:q x∈(transfiniteFiltration p β:AddSubgroup Q):=by
        rw [quotient_filtration_below p K δ le_rfl β hβ.le]
        exact ⟨x,hx,rfl⟩
      simpa only [hzero,AddSubgroup.mem_bot] using hh
    have hb:β+1≤δ:=by simpa only [Order.succ_eq_add_one] using Order.succ_le_of_lt hβ
    have hstable:StableAt p G β:=by
      apply le_antisymm
      · exact hs.trans (transfiniteFiltration_antitone p hb)
      · exact transfiniteFiltration_antitone p le_self_add
    have hbzero:(transfiniteFiltration p β:AddSubgroup G)=⊥:=
      hr _ (primary_stable_stage G p hG β hstable).1
    exact hl β hβ hbzero
  exact ⟨inferInstance,hQ,hred,⟨hz,hlong⟩,
    reduced_long_limit_infinite_socles Q p hQ hred δ hδ hlong⟩
end LogicLineages.ModelsAlgebra.PGroups
