module
public import LogicLineages.ModelsAlgebra.PGroups.TailExactLengthTargets
public import LogicLineages.ModelsAlgebra.PGroups.TransfiniteTail
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

theorem tail_exact_length_transport : Targets.tailExactLengthTransport := by
  classical
  intro G T _ _ _ p δ ell ⟨e⟩ hlen
  let S:AddSubgroup G:=transfiniteFiltration p δ
  have hm (α:Ordinal.{0}):(transfiniteFiltration p α:AddSubgroup S).map e.toAddMonoidHom=
      (transfiniteFiltration p α:AddSubgroup T):=by
    have hk:e.toAddMonoidHom.ker≤(transfiniteFiltration p α:AddSubgroup S):=by
      rw [e.toAddMonoidHom.ker_eq_bot e.injective]
      exact bot_le
    exact map_transfiniteFiltration_below p e.toAddMonoidHom e.surjective α hk α le_rfl
  have hzero:(transfiniteFiltration p ell:AddSubgroup S)=⊥:=by
    apply le_antisymm _ bot_le
    intro x hx
    have he:e x∈(transfiniteFiltration p ell:AddSubgroup T):=by
      rw [←hm ell]
      exact ⟨x,hx,rfl⟩
    rw [hlen.1,AddSubgroup.mem_bot] at he
    change x=0
    exact e.injective (he.trans e.map_zero.symm)
  have hnonzero:∀α<ell,(transfiniteFiltration p α:AddSubgroup S)≠⊥:=by
    intro α hα hz
    have he:(transfiniteFiltration p α:AddSubgroup T)=⊥:=by
      rw [←hm α,hz,AddSubgroup.map_bot]
    exact hlen.2 α hα he
  constructor
  · rw [←transfinite_tail_image G p δ ell,hzero,AddSubgroup.map_bot]
  · intro α hα hz
    by_cases hsmall:α<δ
    · obtain ⟨t,ht⟩:=exists_ne (0:T)
      let x:S:=e.symm t
      have hx:x≠0:=by
        intro hx
        apply ht
        have he:=congrArg e hx
        simpa only [x,e.apply_symm_apply,e.map_zero] using he
      have hm:(x:G)∈(transfiniteFiltration p α:AddSubgroup G):=
        transfiniteFiltration_antitone p hsmall.le x.property
      rw [hz,AddSubgroup.mem_bot] at hm
      exact hx (Subtype.ext hm)
    · have hδα:δ≤α:=le_of_not_gt hsmall
      have he:δ+(α-δ)=α:=Ordinal.add_sub_cancel_of_le hδα
      have hb:α-δ<ell:=by
        apply (add_lt_add_iff_left δ).mp
        simpa only [he] using hα
      apply hnonzero (α-δ) hb
      apply le_antisymm _ bot_le
      intro x hx
      have hm:=(transfinite_tail_membership G p δ (α-δ) x).mp hx
      rw [he,hz,AddSubgroup.mem_bot] at hm
      exact Subtype.ext hm
end LogicLineages.ModelsAlgebra.PGroups
