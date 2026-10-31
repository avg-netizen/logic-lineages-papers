module
public import LogicLineages.ModelsAlgebra.PGroups.DivisibleCharacteristicTargets
public import LogicLineages.ModelsAlgebra.PGroups.DivisiblePartProof
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

private theorem divisible_range {G H : Type} [AddCommGroup G] [AddCommGroup H]
    (f : G →+ H) (hd : GroupDivisible G) : SubgroupDivisible f.range := by
  intro n hn x
  obtain ⟨a,ha⟩ := x.property
  obtain ⟨b,hb⟩ := hd n hn a
  refine ⟨⟨f b,⟨b,rfl⟩⟩,Subtype.ext ?_⟩
  change n • f b = (x:H)
  rw [←map_nsmul,hb,ha]

private theorem maps_divisible_part {G H : Type} [AddCommGroup G] [AddCommGroup H]
    (f : G →+ H) (x : divisiblePart G) : f (x:G) ∈ divisiblePart H := by
  let g := f.comp (divisiblePart G).subtype
  have hle := (actual_divisible_part H).2 g.range
    (divisible_range g (actual_divisible_part G).1)
  exact hle ⟨x,rfl⟩

theorem divisible_part_characteristic : Targets.divisiblePartCharacteristic := by
  intro G H _ _ e
  let d : divisiblePart G ≃+ divisiblePart H :=
    { toFun := fun x => ⟨e x,maps_divisible_part e.toAddMonoidHom x⟩
      invFun := fun x => ⟨e.symm x,maps_divisible_part e.symm.toAddMonoidHom x⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x)
      right_inv := fun x => Subtype.ext (e.apply_symm_apply x)
      map_add' := fun x y => Subtype.ext (e.map_add x y) }
  exact ⟨d,fun _ => rfl⟩

theorem reduced_divisible_product_part : Targets.reducedDivisibleProductPart := by
  intro R D _ _ hr hd
  let i : D →+ R × D := AddMonoidHom.inr R D
  have hi : ∀ x : D, i x ∈ divisiblePart (R×D) := by
    intro x
    exact (actual_divisible_part (R×D)).2 i.range (divisible_range i hd) ⟨x,rfl⟩
  let j : D →+ divisiblePart (R×D) := i.codRestrict _ hi
  have hj : Function.Injective j := by
    intro x y h
    exact congrArg (fun z : divisiblePart (R×D) => (z:R×D).2) h
  let q : divisiblePart (R×D) →+ R :=
    (AddMonoidHom.fst R D).comp (divisiblePart (R×D)).subtype
  have hz : q.range = ⊥ := hr q.range (divisible_range q (actual_divisible_part (R×D)).1)
  have hsur : Function.Surjective j := by
    intro x
    have hx : q x ∈ q.range := ⟨x,rfl⟩
    rw [hz,AddSubgroup.mem_bot] at hx
    refine ⟨(x:R×D).2,Subtype.ext ?_⟩
    exact Prod.ext hx.symm rfl
  exact ⟨AddEquiv.ofBijective j ⟨hj,hsur⟩,fun _ => rfl⟩

private def top_socle_equiv {D E : Type} [AddCommGroup D] [AddCommGroup E]
    (p : ℕ) (e : D ≃+ E) :
    pSocle p (⊤ : AddSubgroup D) ≃+ pSocle p (⊤ : AddSubgroup E) where
  toFun x := ⟨e x,AddSubgroup.mem_top _,by
    change p • e (x:D) = 0
    have hx : p • (x:D) = 0 := x.property.2
    rw [←map_nsmul,hx,map_zero]⟩
  invFun x := ⟨e.symm x,AddSubgroup.mem_top _,by
    change p • e.symm (x:E) = 0
    have hx : p • (x:E) = 0 := x.property.2
    rw [←map_nsmul,hx,map_zero]⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv x := Subtype.ext (e.apply_symm_apply x)
  map_add' x y := Subtype.ext (e.map_add x y)

theorem divisible_product_socle_invariant : Targets.divisibleProductSocleInvariant := by
  intro R S D E _ _ _ _ hr hs hd he p ⟨f⟩
  obtain ⟨i,_⟩ := reduced_divisible_product_part R D hr hd
  obtain ⟨j,_⟩ := reduced_divisible_product_part S E hs he
  obtain ⟨k,_⟩ := divisible_part_characteristic (R×D) (S×E) f
  exact ⟨top_socle_equiv p ((i.trans k).trans j.symm)⟩
end LogicLineages.ModelsAlgebra.PGroups
