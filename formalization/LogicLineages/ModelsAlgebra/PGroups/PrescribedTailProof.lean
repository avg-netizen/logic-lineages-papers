module
public import LogicLineages.ModelsAlgebra.PGroups.PrescribedTailTargets
public import LogicLineages.ModelsAlgebra.PGroups.PrimaryDivisibleEmbeddingProof
public import LogicLineages.ModelsAlgebra.PGroups.CofinalSocleMapProof
public import LogicLineages.ModelsAlgebra.PGroups.SoclePullbackProof
public import LogicLineages.ModelsAlgebra.PGroups.ReducedLimitTruncationProof
public import LogicLineages.ModelsAlgebra.PGroups.TailExactLengthProof
public import LogicLineages.ModelsAlgebra.PGroups.FullQuotientFiltration
public import Mathlib.SetTheory.Cardinal.Arithmetic
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

private theorem surjective_omega_cut_rank {A B:Type} [AddCommGroup A] [AddCommGroup B]
    (p:ℕ) [Fact p.Prime] (f:A→+B) (hf:Function.Surjective f) (γ:Ordinal.{0})
    (hk:f.ker≤(transfiniteFiltration p (Ordinal.omega0*γ):AddSubgroup A))
    (α:Ordinal.{0}) (hα:α<Ordinal.omega0*γ) :
    Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α:AddSubgroup A))=
      Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α:AddSubgroup B)) := by
  let S:AddSubgroup A:=transfiniteFiltration p α
  have hdeep:f.ker≤pStep p (pStep p S):=by
    rw [←transfiniteFiltration_add_two]
    exact hk.trans (transfiniteFiltration_antitone p (omegaCut_two_steps_lt hα).le)
  let e₁:=LinearEquiv.ofBijective (ulmMap p S f) (UlmLocal.ulmMap_bijective p S f hdeep)
  have hm:=map_transfiniteFiltration_below p f hf (Ordinal.omega0*γ) hk α hα.le
  let e₂:=ulmLayerCongr p hm
  exact (e₁.trans e₂).rank_eq

/-- A direct actual pullback realization of the prescribed tail. The only
countable choices enumerate actual stage-socle requirements. No general
factor-sequence realization theorem is assumed. -/
theorem transfinite_prescribed_tail_existence : Targets.transfinitePrescribedTailExistence := by
  classical
  intro p _ G T _ _ _ _ _ γ _ ellG ellT hG hT hrG hrT hγ hlG hlong hlT
  let δ:=Ordinal.omega0*γ
  have hp:p≠0:=(Fact.out:p.Prime).ne_zero
  have hδ:Order.IsSuccLimit δ:=Ordinal.isSuccLimit_mul_left Ordinal.isSuccLimit_omega0 hγ
  have hδpos:0<δ:=mul_pos Ordinal.omega0_pos hγ
  letI:Countable δ.ToType:=by
    apply Cardinal.mk_le_aleph0_iff.mp
    rw [Cardinal.mk_toType,Ordinal.card_mul,Ordinal.card_omega0]
    have hh:γ.card≤Cardinal.aleph0:=by
      simpa only [Cardinal.mk_toType] using Cardinal.mk_le_aleph0 (α:=γ.ToType)
    exact (mul_le_mul_left' hh Cardinal.aleph0).trans_eq Cardinal.aleph0_mul_aleph0
  let K:AddSubgroup G:=transfiniteFiltration p δ
  let B:=G⧸K
  have hlongG:StagesNonzeroBelow p G δ:=fun α hα=>hlG.2 α (hα.trans_le hlong)
  obtain ⟨hBc,hB,hBr,hlB,hBs⟩:=actual_reduced_limit_truncation p G δ hδ hG hrG hlongG
  letI:Countable B:=hBc
  obtain ⟨E,instE,he⟩:=countable_primary_divisible_embedding p T hT
  letI:AddCommGroup E:=instE
  obtain ⟨hEc,hE,hEd,i,hi⟩:=he
  letI:Countable E:=hEc
  let C:=E⧸i.range
  let q:E→+C:=QuotientAddGroup.mk' i.range
  have hq:Function.Surjective q:=QuotientAddGroup.mk'_surjective i.range
  letI:Countable C:=hq.countable
  have hCd:GroupDivisible C:=by
    intro n hn x
    obtain ⟨e,rfl⟩:=hq x
    obtain ⟨y,hy⟩:=hEd n hn e
    refine ⟨q y,?_⟩
    rw [←map_nsmul,hy]
  obtain ⟨f,hf⟩:=cofinal_socle_surjective_hom p B C δ hδpos hCd hBs
  let H:=HomPullback f q
  let π:H→+B:=pullbackProjection f q
  obtain ⟨hπ,hfil⟩:=actual_socle_pullback_filtration p B C E f q δ hp hq hEd hf
  letI:Countable H:=inferInstance
  have hH:∀x:H,∃k:ℕ,p^k • x=0:=by
    intro x
    obtain ⟨k,hk⟩:=hB x.val.1
    obtain ⟨j,hj⟩:=hE x.val.2
    refine ⟨k+j,Subtype.ext (Prod.ext ?_ ?_)⟩
    · change p^(k+j) • x.val.1=0
      rw [pow_add,mul_nsmul,hk,nsmul_zero]
    · change p^(k+j) • x.val.2=0
      rw [Nat.add_comm k j,pow_add,mul_nsmul,hj,nsmul_zero]
  have hkπ:π.ker≤(transfiniteFiltration p δ:AddSubgroup H):=by
    intro x hx
    apply (hfil δ le_rfl x).mpr
    change x.val.1=0 at hx
    rw [hx]
    exact AddSubgroup.zero_mem _
  let S:AddSubgroup H:=transfiniteFiltration p δ
  let j:T→+H:={
    toFun:=fun t=>⟨(0,i t),by
      change f 0=q (i t)
      rw [map_zero]
      symm
      exact (QuotientAddGroup.eq_zero_iff _).mpr ⟨t,rfl⟩⟩
    map_zero':=by apply Subtype.ext;change (0,i 0)=(0,0);simp
    map_add':=by intro x y;apply Subtype.ext;change (0,i (x+y))=(0,i x)+(0,i y);simp}
  have hjS:∀t:T,j t∈S:=by
    intro t
    apply (hfil δ le_rfl (j t)).mpr
    exact AddSubgroup.zero_mem _
  let k:T→+S:=j.codRestrict S hjS
  have hki:Function.Injective k:=by
    intro t u htu
    apply hi
    exact congrArg (fun z:S=>z.val.val.2) htu
  have hks:Function.Surjective k:=by
    intro x
    have hx:x.val.val.1=0:=by
      have hh:=(hfil δ le_rfl x.val).mp x.property
      simpa only [hlB.1,AddSubgroup.mem_bot] using hh
    have hxe:q x.val.val.2=0:=by
      have hh:=x.val.property
      change f x.val.val.1=q x.val.val.2 at hh
      rw [hx,map_zero] at hh
      exact hh.symm
    have hmem:x.val.val.2∈i.range:=(QuotientAddGroup.eq_zero_iff _).mp hxe
    obtain ⟨t,ht⟩:=hmem
    refine ⟨t,?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext hx.symm ht
  let e:T≃+S:=AddEquiv.ofBijective k ⟨hki,hks⟩
  have heTail:Nonempty (S≃+T):=⟨e.symm⟩
  have hlH:PGroupExactLength p H (δ+ellT):=tail_exact_length_transport H T p δ ellT heTail hlT
  have hredH:IsReducedAddGroup H:=zero_stage_reduced H p hp (δ+ellT) hlH.1
  refine ⟨H,inferInstance,inferInstance,hH,hredH,?_,heTail,hlH⟩
  intro α hα
  have hGB:=((full_quotient_filtration p K γ le_rfl).2 α hα).2
  have hHB:=surjective_omega_cut_rank p π hπ γ hkπ α hα
  exact hGB.trans hHB.symm
end LogicLineages.ModelsAlgebra.PGroups
