module
public import LogicLineages.ModelsAlgebra.PGroups.PrimaryTailCategoricityTargets
public import LogicLineages.ModelsAlgebra.PGroups.PrimaryUlmClassificationProof
public import LogicLineages.ModelsAlgebra.PGroups.TransfiniteTailUlm
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

private theorem divisible_range {G H:Type} [AddCommGroup G] [AddCommGroup H]
    (f:G→+H) (hd:SubgroupDivisible (⊤:AddSubgroup G)) : SubgroupDivisible f.range := by
  intro n hn x
  obtain ⟨a,ha⟩ := x.property
  obtain ⟨b,hb⟩ := hd n hn ⟨a,AddSubgroup.mem_top _⟩
  refine ⟨⟨f b,⟨b,rfl⟩⟩,Subtype.ext ?_⟩
  change n • f (b:G)=(x:H)
  have hb' : n • (b:G)=a := congrArg (fun z:(⊤:AddSubgroup G)=>(z:G)) hb
  rw [←map_nsmul,hb',ha]

private theorem maps_divisible {G H:Type} [AddCommGroup G] [AddCommGroup H]
    (f:G→+H) : ∀x:divisiblePart G, f (x:G) ∈ divisiblePart H := by
  let g := f.comp (divisiblePart G).subtype
  have hd : SubgroupDivisible (⊤:AddSubgroup (divisiblePart G)) := by
    intro n hn x
    obtain ⟨y,hy⟩ := (actual_divisible_part G).1 n hn x
    exact ⟨⟨y,AddSubgroup.mem_top _⟩,Subtype.ext hy⟩
  intro x
  exact (actual_divisible_part H).2 g.range (divisible_range g hd) ⟨x,rfl⟩

theorem divisible_part_in_subgroup : Targets.divisiblePartInSubgroup := by
  intro G _ S hS
  let j : divisiblePart G →+ S :=
    { toFun:=fun x=>⟨x,hS x.property⟩,map_zero':=rfl,map_add':=fun _ _=>rfl }
  have hj : ∀x, j x ∈ divisiblePart S := by
    have hd : SubgroupDivisible (⊤:AddSubgroup (divisiblePart G)) := by
      intro n hn x
      obtain ⟨y,hy⟩ := (actual_divisible_part G).1 n hn x
      exact ⟨⟨y,AddSubgroup.mem_top _⟩,Subtype.ext hy⟩
    intro x
    exact (actual_divisible_part S).2 j.range (divisible_range j hd) ⟨x,rfl⟩
  let e : divisiblePart G ≃+ divisiblePart S :=
    { toFun:=fun x=>⟨j x,hj x⟩
      invFun:=fun x=>⟨((x:S):G),maps_divisible S.subtype x⟩
      left_inv:=fun _=>rfl
      right_inv:=fun _=>rfl
      map_add':=fun _ _=>rfl }
  exact ⟨e,fun _=>rfl⟩

private theorem socle_rank (G H:Type) [AddCommGroup G] [AddCommGroup H] (p:ℕ)
    (S:AddSubgroup G) (T:AddSubgroup H) (e:S≃+T) :
    Module.rank (ZMod p) (pSocle p S)=Module.rank (ZMod p) (pSocle p T) := by
  let u : pSocle p S ≃+ pSocle p T :=
    { toFun:=fun x=>⟨(e ⟨x,x.property.1⟩:H),(e ⟨x,x.property.1⟩).property,by
        have hx:p • (⟨(x:G),x.property.1⟩:S)=0 := Subtype.ext x.property.2
        have hh := congrArg (fun z:T=>(z:H)) (by rw [←map_nsmul,hx,map_zero] : p • e ⟨x,x.property.1⟩=0)
        exact hh⟩
      invFun:=fun x=>⟨(e.symm ⟨x,x.property.1⟩:G),(e.symm ⟨x,x.property.1⟩).property,by
        have hx:p • (⟨(x:H),x.property.1⟩:T)=0 := Subtype.ext x.property.2
        exact congrArg (fun z:S=>(z:G)) (by rw [←map_nsmul,hx,map_zero] : p • e.symm ⟨x,x.property.1⟩=0)⟩
      left_inv:=fun x=>Subtype.ext (congrArg (fun z:S=>(z:G)) (e.symm_apply_apply ⟨x,x.property.1⟩))
      right_inv:=fun x=>Subtype.ext (congrArg (fun z:T=>(z:H)) (e.apply_symm_apply ⟨x,x.property.1⟩))
      map_add':=fun x y=>Subtype.ext (congrArg (fun z:T=>(z:H)) (e.map_add ⟨x,x.property.1⟩ ⟨y,y.property.1⟩)) }
  exact (LinearEquiv.ofBijective (u.toAddMonoidHom.toZModLinearMap p) u.bijective).rank_eq

private theorem rank_invariant (p:ℕ) (G H:Type) [AddCommGroup G] [AddCommGroup H]
    (e:G≃+H) (α:Ordinal.{0}) :
    Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α:AddSubgroup G)) =
    Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α:AddSubgroup H)) := by
  have hk : e.toAddMonoidHom.ker ≤ (transfiniteFiltration p α:AddSubgroup G) := by
    rw [e.toAddMonoidHom.ker_eq_bot e.injective];exact bot_le
  have hm := map_transfiniteFiltration_below p e.toAddMonoidHom e.surjective α hk α le_rfl
  obtain ⟨u⟩ := GroupInfinitary.injective_ulm_isomorphism G H p (transfiniteFiltration p α) e.toAddMonoidHom e.injective
  rw [hm] at u
  exact u.rank_eq

theorem primary_tail_categoricity : Targets.primaryTailCategoricity := by
  intro G H _ _ _ _ p _ hG hH δ e hbelow
  apply (countable_primary_ulm_classification G H p hG hH).mpr
  constructor
  · intro α
    by_cases ha:α<δ
    · exact hbelow α ha
    · have he:=rank_invariant p _ _ e (α-δ)
      rw [transfinite_tail_ulm_rank G p δ (α-δ),transfinite_tail_ulm_rank H p δ (α-δ),
        Ordinal.add_sub_cancel_of_le (le_of_not_gt ha)] at he
      exact he
  · have hD (A:Type) [AddCommGroup A] : divisiblePart A ≤ (transfiniteFiltration p δ:AddSubgroup A) :=
      p_divisible_in_every_stage A p (divisiblePart A)
        ((actual_divisible_part A).1 p (Fact.out:p.Prime).ne_zero) δ
    obtain ⟨i,_⟩ := divisible_part_in_subgroup G _ (hD G)
    obtain ⟨j,_⟩ := divisible_part_in_subgroup H _ (hD H)
    obtain ⟨k,_⟩ := divisible_part_characteristic _ _ e
    exact socle_rank G H p (divisiblePart G) (divisiblePart H) ((i.trans k).trans j.symm)
end LogicLineages.ModelsAlgebra.PGroups
