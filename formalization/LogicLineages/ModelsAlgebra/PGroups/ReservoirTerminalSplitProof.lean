module
public import LogicLineages.ModelsAlgebra.PGroups.ReservoirTerminalSplitTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
open GroupInfinitary

theorem reservoir_complement_split : Targets.reservoirComplementSplit := by
  classical
  intro A B C _ _ _ i
  refine ⟨?_,?_,?_⟩
  · apply AddSubgroup.disjoint_def.mpr
    intro x hx ht
    apply Prod.ext ht.1
    apply Prod.ext _ ht.2.2
    ext n
    by_cases hn : n<i
    · exact ht.2.1 n hn
    · exact hx n (Nat.le_of_not_gt hn)
  · apply top_unique
    intro x _
    let y : ReservoirGroup A B C := (x.1,(x.2.1.filter (fun n => n<i),x.2.2))
    let z : ReservoirGroup A B C := (0,(x.2.1.filter (fun n => ¬n<i),0))
    refine AddSubgroup.mem_sup.mpr ⟨y,?_,z,?_,?_⟩
    · intro n hn
      change (if n<i then x.2.1 n else 0)=0
      exact if_neg (not_lt_of_ge hn)
    · refine ⟨rfl,?_,rfl⟩
      intro n hn
      change (if ¬n<i then x.2.1 n else 0)=0
      exact if_neg (not_not.mpr hn)
    · apply Prod.ext (add_zero _)
      exact Prod.ext (Finsupp.filter_add_filter_not x.2.1 (fun n => n<i)) (add_zero _)
  · intro d hd x
    apply Subtype.ext
    apply Prod.ext
    · change d • x.val.1=0
      rw [x.property.1,nsmul_zero]
    · apply Prod.ext
      · ext n
        exact hd (x.val.2.1 n)
      · change d • x.val.2.2=0
        rw [x.property.2.2,nsmul_zero]

theorem reservoir_ambient_split : Targets.reservoirAmbientSplit := by
  classical
  intro G A B C _ _ _ _ S e i d hd
  let R := ReservoirGroup A B C
  let f : R →+ G := S.subtype.comp e.symm.toAddMonoidHom
  have hf : Function.Injective f := by
    intro x y h
    exact e.symm.injective (Subtype.ext h)
  let K0 := reservoirStage A B C i
  let T0 := reservoirComplement A B C i
  let K := K0.map f
  let T := T0.map f
  have hh := reservoir_complement_split A B C i
  have hrange : f.range = S := by
    apply le_antisymm
    · rintro x ⟨y,rfl⟩; exact (e.symm y).property
    · intro x hx
      exact ⟨e ⟨x,hx⟩,by change (e.symm (e ⟨x,hx⟩):G)=x; rw [AddEquiv.symm_apply_apply]⟩
  have hsum : S=K⊔T := by
    change S=K0.map f ⊔ T0.map f
    rw [← AddSubgroup.map_sup,hh.2.1,← AddMonoidHom.range_eq_map,hrange]
  have hbound : ∀ x : T, d • x=0 := by
    intro x
    obtain ⟨y,hy,he⟩ := x.property
    have hz := (hh.2.2 d hd) ⟨y,hy⟩
    apply Subtype.ext
    change d • (x:G)=0
    rw [← he,← map_nsmul]
    have hy0 : d • y=0 := congrArg (fun z : T0 => (z:R)) hz
    rw [hy0,map_zero]
  refine ⟨K,T,hsum,AddSubgroup.disjoint_map hf hh.1,
    ⟨(AddSubgroup.equivMapOfInjective K0 f hf).symm⟩,hbound,?_⟩
  intro x
  constructor
  · rintro ⟨y,hy,he⟩
    have he' : e.symm y=x := Subtype.ext he
    have hxy : e x=y := by rw [← he',AddEquiv.apply_symm_apply]
    rw [hxy]
    exact hy
  · intro hx
    exact ⟨e x,hx,by change (e.symm (e x):G)=(x:G); rw [AddEquiv.symm_apply_apply]⟩
end LogicLineages.ModelsAlgebra.PGroups
