module
public import LogicLineages.ModelsAlgebra.PGroups.PrimaryUlmClassificationTargets
public import LogicLineages.ModelsAlgebra.PGroups.DivisibleSplittingProof
public import LogicLineages.ModelsAlgebra.PGroups.DivisibleCharacteristicProof
public import LogicLineages.ModelsAlgebra.PGroups.DivisiblePrueferProof
public import LogicLineages.ModelsAlgebra.PGroups.ReducedUlmClassificationProof
public import LogicLineages.ModelsAlgebra.PGroups.ProductTransfiniteProof
public import LogicLineages.ModelsAlgebra.PGroups.SocleUlmVanishing
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

private theorem primary_subgroup (G:Type) [AddCommGroup G] (p:ℕ)
    (hp:∀x:G,∃k:ℕ,p^k • x=0) (S:AddSubgroup G) : ∀x:S,∃k:ℕ,p^k • x=0 := by
  intro x
  obtain ⟨k,hk⟩ := hp x
  exact ⟨k,Subtype.ext hk⟩

private theorem rank_invariant (p:ℕ) (G H:Type) [AddCommGroup G] [AddCommGroup H]
    (e:G≃+H) (α:Ordinal.{0}) :
    Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α:AddSubgroup G)) =
    Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α:AddSubgroup H)) := by
  have hk : e.toAddMonoidHom.ker ≤ (transfiniteFiltration p α : AddSubgroup G) := by
    rw [e.toAddMonoidHom.ker_eq_bot e.injective]
    exact bot_le
  have hm := map_transfiniteFiltration_below p e.toAddMonoidHom e.surjective α hk α le_rfl
  have hu := GroupInfinitary.injective_ulm_isomorphism G H p
    (transfiniteFiltration p α) e.toAddMonoidHom e.injective
  rw [hm] at hu
  obtain ⟨u⟩ := hu
  exact u.rank_eq

private theorem product_rank (R D:Type) [AddCommGroup R] [AddCommGroup D]
    (p:ℕ) [Fact p.Prime] (hd:GroupDivisible D) (α:Ordinal.{0}) :
    Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α:AddSubgroup (R×D))) =
    Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α:AddSubgroup R)) := by
  have ht : (transfiniteFiltration p α:AddSubgroup D)=⊤ := by
    apply top_unique
    apply p_divisible_in_every_stage D p ⊤ _ α
    intro x
    obtain ⟨y,hy⟩ := hd p (Fact.out : p.Prime).ne_zero x
    exact ⟨⟨y,AddSubgroup.mem_top _⟩,Subtype.ext hy⟩
  rw [product_transfinite_ulm_rank,ht]
  have hz : Module.rank (ZMod p) (UlmLayer p (⊤:AddSubgroup D))=0 := by
    apply (GroupInfinitary.ulm_rank_zero_socle p D ⊤).mpr
    intro x _
    obtain ⟨y,hy⟩ := hd p (Fact.out : p.Prime).ne_zero x
    exact ⟨y,AddSubgroup.mem_top _,hy⟩
  rw [hz,add_zero]

private theorem subgroup_socle_rank (G:Type) [AddCommGroup G] (p:ℕ) (S:AddSubgroup G) :
    Module.rank (ZMod p) (pSocle p (⊤:AddSubgroup S)) = Module.rank (ZMod p) (pSocle p S) := by
  let e : pSocle p (⊤:AddSubgroup S) ≃+ pSocle p S :=
    { toFun := fun x => ⟨((x:S):G),(x:S).property,
        congrArg (fun z:S => (z:G)) x.property.2⟩
      invFun := fun x => ⟨⟨(x:G),x.property.1⟩,AddSubgroup.mem_top _,Subtype.ext x.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  let l := LinearEquiv.ofBijective (e.toAddMonoidHom.toZModLinearMap p) e.bijective
  exact l.rank_eq

theorem countable_primary_ulm_classification : Targets.countablePrimaryUlmClassification := by
  intro G H _ _ _ _ p _ hG hH
  have hpG := primary_subgroup G p hG
  have hpH := primary_subgroup H p hH
  have dG : GroupDivisible (divisiblePart G) := (actual_divisible_part G).1
  have dH : GroupDivisible (divisiblePart H) := (actual_divisible_part H).1
  constructor
  · rintro ⟨e⟩
    refine ⟨fun α=>rank_invariant p G H e α,?_⟩
    obtain ⟨d,_⟩ := divisible_part_characteristic G H e
    have hd := (divisible_primary_classification p (divisiblePart G) (divisiblePart H)
      (hpG _) (hpH _) dG dH).mp ⟨d⟩
    exact (subgroup_socle_rank G p (divisiblePart G)).symm.trans
      (hd.trans (subgroup_socle_rank H p (divisiblePart H)))
  · rintro ⟨hu,hd⟩
    obtain ⟨_,R,_,_,hr,_,_,eG,_⟩ := actual_divisible_splitting G
    obtain ⟨_,S,_,_,hs,_,_,eH,_⟩ := actual_divisible_splitting H
    have hrank : ∀α:Ordinal.{0},
        Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α:AddSubgroup R)) =
        Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α:AddSubgroup S)) := by
      intro α
      exact (product_rank R (divisiblePart G) p dG α).symm.trans
        ((rank_invariant p _ _ eG α).trans ((hu α).trans
          ((rank_invariant p _ _ eH α).symm.trans (product_rank S (divisiblePart H) p dH α))))
    obtain ⟨r⟩ := (countable_reduced_ulm_classification R S p (hpG R) (hpH S) hr hs).mpr hrank
    have hdiv : Module.rank (ZMod p) (pSocle p (⊤:AddSubgroup (divisiblePart G))) =
        Module.rank (ZMod p) (pSocle p (⊤:AddSubgroup (divisiblePart H))) :=
      (subgroup_socle_rank G p (divisiblePart G)).trans (hd.trans (subgroup_socle_rank H p (divisiblePart H)).symm)
    obtain ⟨d⟩ := (divisible_primary_classification p (divisiblePart G) (divisiblePart H)
      (hpG _) (hpH _) dG dH).mpr hdiv
    exact ⟨(eG.symm.trans (r.prodCongr d)).trans eH⟩
end LogicLineages.ModelsAlgebra.PGroups
