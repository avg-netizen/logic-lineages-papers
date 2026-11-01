module
public import LogicLineages.ModelsAlgebra.PGroups.PrescribedTailTargets
public import LogicLineages.ModelsAlgebra.PGroups.FullQuotientFiltration
public import LogicLineages.ModelsAlgebra.PGroups.TransfiniteTail
public import LogicLineages.ModelsAlgebra.PGroups.TransfiniteTailUlm
public import LogicLineages.ModelsAlgebra.PGroups.FiniteOrdinalFiltration
public import LogicLineages.ModelsAlgebra.PGroups.ImageCardinality
public import LogicLineages.ModelsAlgebra.PGroups.PPrimaryQuotient
public import LogicLineages.ModelsAlgebra.PGroups.StableStageProof
public import LogicLineages.ModelsAlgebra.PGroups.ZeroStageReduced
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

/-- Every actual Ulm factor has zero omega stage, independently of reducedness. -/
theorem ulm_factor_omega_zero (G:Type) [AddCommGroup G] (p:ℕ) [Fact p.Prime]
    (ξ:Ordinal.{0}) :
    (transfiniteFiltration p (Ordinal.omega0:Ordinal.{0}):AddSubgroup (UlmFactor p G ξ))=⊥ := by
  let S:AddSubgroup G:=transfiniteFiltration p (Ordinal.omega0*ξ)
  let U:AddSubgroup S:=transfiniteFiltration p (Ordinal.omega0:Ordinal.{0})
  have hT:U≤(transfiniteFiltration p (Ordinal.omega0*1):AddSubgroup S):=by simpa only [mul_one] using (le_refl U)
  have hf:=full_quotient_filtration p U (1:Ordinal.{0}) hT
  have he:=hf.1 Ordinal.omega0 (by simp)
  change (transfiniteFiltration p Ordinal.omega0:AddSubgroup (S⧸U))=⊥
  rw [he]
  apply le_antisymm _ bot_le
  rintro x ⟨y,hy,rfl⟩
  exact (QuotientAddGroup.eq_zero_iff _).mpr hy

theorem initial_ulm_factor_admissibility : Targets.initialUlmFactorAdmissibility := by
  classical
  intro p _ G _ _ γ hG hr hlong ξ hξ
  let cut:=Ordinal.omega0*ξ
  let S:AddSubgroup G:=transfiniteFiltration p cut
  let U:AddSubgroup S:=transfiniteFiltration p (Ordinal.omega0:Ordinal.{0})
  let q:=QuotientAddGroup.mk' U
  let C:=S⧸U
  letI:Countable C:=(QuotientAddGroup.mk'_surjective U).countable
  have hS:∀x:S,∃k:ℕ,p^k • x=0:=by
    intro x
    obtain ⟨k,hk⟩:=hG (x:G)
    exact ⟨k,Subtype.ext hk⟩
  have hC:=p_primary_quotient S p U hS
  refine ⟨inferInstance,hC,zero_stage_reduced C p (Fact.out:p.Prime).ne_zero Ordinal.omega0
    (ulm_factor_omega_zero G p ξ),?_,?_⟩
  · intro N
    by_contra! hbound
    have hSN:(transfiniteFiltration p (N:Ordinal.{0}):AddSubgroup S)≤U:=by
      intro x hx
      rw [finite_ordinal_filtration,GroupInfinitary.finite_filtration_multiple_image] at hx
      obtain ⟨y,rfl⟩:=hx
      apply (QuotientAddGroup.eq_zero_iff _).mp
      change q (p^N • y)=0
      rw [map_nsmul]
      exact hbound (q y)
    have hs:StableAt p S (N:Ordinal.{0}):=by
      apply le_antisymm
      · exact hSN.trans (transfiniteFiltration_antitone p
          (by simpa only [Nat.cast_add,Nat.cast_one] using (Ordinal.natCast_lt_omega0 (N+1)).le))
      · exact transfiniteFiltration_antitone p le_self_add
    have hg:StableAt p G (cut+N):=by
      have he:=congrArg (fun A:AddSubgroup S=>A.map S.subtype) hs
      rw [transfinite_tail_image,transfinite_tail_image] at he
      simpa only [StableAt,add_assoc] using he
    have hz:(transfiniteFiltration p (cut+N):AddSubgroup G)=⊥ :=
      hr _ (primary_stable_stage G p hG (cut+N) hg).1
    have hstrict:cut+(N:Ordinal.{0})<Ordinal.omega0*γ:=by
      have hω:cut+(N:Ordinal.{0})<cut+Ordinal.omega0:=
        (add_lt_add_iff_left cut).mpr (Ordinal.natCast_lt_omega0 N)
      have hmul:cut+Ordinal.omega0≤Ordinal.omega0*γ:=by
        simpa only [cut,Order.succ_eq_add_one,mul_add_one] using
          mul_le_mul_left' (Order.succ_le_of_lt hξ) Ordinal.omega0
      exact hω.trans_le hmul
    exact hlong (cut+N) hstrict hz
  · intro n
    have hT:U≤(transfiniteFiltration p (Ordinal.omega0*1):AddSubgroup S):=by simpa only [mul_one] using (le_refl U)
    have hf:=full_quotient_filtration p U (1:Ordinal.{0}) hT
    have hn:(n:Ordinal.{0})<Ordinal.omega0*1:=by simpa only [mul_one] using Ordinal.natCast_lt_omega0 n
    exact ((hf.2 (n:Ordinal.{0}) hn).2).symm.trans (transfinite_tail_ulm_rank G p cut (n:Ordinal.{0}))
end LogicLineages.ModelsAlgebra.PGroups
