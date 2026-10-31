module
public import LogicLineages.ModelsAlgebra.PGroups.ProductSubgroupSplitTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

theorem product_subgroup_split : Targets.productSubgroupSplit := by
  classical
  intro G A B _ _ _ S e
  let f : A →+ G := S.subtype.comp (e.symm.toAddMonoidHom.comp (AddMonoidHom.inl A B))
  let g : B →+ G := S.subtype.comp (e.symm.toAddMonoidHom.comp (AddMonoidHom.inr A B))
  have hf : Function.Injective f := by
    intro a b h
    have he : e.symm (a,0) = e.symm (b,0) := Subtype.ext h
    exact congrArg Prod.fst (e.symm.injective he)
  have hg : Function.Injective g := by
    intro a b h
    have he : e.symm (0,a) = e.symm (0,b) := Subtype.ext h
    exact congrArg Prod.snd (e.symm.injective he)
  let K := f.range
  let T := g.range
  have hKS : K ≤ S := by rintro y ⟨a,rfl⟩; exact (e.symm (a,0)).property
  have hTS : T ≤ S := by rintro y ⟨b,rfl⟩; exact (e.symm (0,b)).property
  have hs : S=K⊔T := by
    apply le_antisymm _ (sup_le hKS hTS)
    intro y hy
    let z : S := ⟨y,hy⟩
    refine AddSubgroup.mem_sup.mpr ⟨f (e z).1,⟨(e z).1,rfl⟩,g (e z).2,⟨(e z).2,rfl⟩,?_⟩
    change (e.symm ((e z).1,0):G)+(e.symm (0,(e z).2):G)=y
    have heq : ((e z).1,0)+(0,(e z).2) = e z := by ext <;> simp
    have hh := e.symm.map_add ((e z).1,0) (0,(e z).2)
    rw [heq] at hh
    exact (congrArg (fun w : S => (w:G)) hh).symm.trans
      (congrArg (fun w : S => (w:G)) (e.symm_apply_apply z))
  have hd : Disjoint K T := by
    apply AddSubgroup.disjoint_def.mpr
    intro y hy ht
    obtain ⟨a,ha⟩ := hy
    obtain ⟨b,hb⟩ := ht
    have he : e.symm (a,0) = e.symm (0,b) := Subtype.ext (ha.trans hb.symm)
    have hz : a=0 := congrArg Prod.fst (e.symm.injective he)
    rw [hz,map_zero] at ha
    exact ha.symm
  refine ⟨K,T,hs,hd,⟨(AddMonoidHom.ofInjective hf).symm⟩,⟨(AddMonoidHom.ofInjective hg).symm⟩,?_⟩
  intro x
  constructor
  · rintro ⟨a,ha⟩
    have he : e.symm (a,0)=x := Subtype.ext ha
    have hh := congrArg e he
    simpa only [AddEquiv.apply_symm_apply] using (congrArg Prod.snd hh).symm
  · intro hx
    refine ⟨(e x).1,?_⟩
    change (e.symm ((e x).1,0):G)=(x:G)
    have he : ((e x).1,0) = e x := Prod.ext rfl hx.symm
    rw [he,AddEquiv.symm_apply_apply]
end LogicLineages.ModelsAlgebra.PGroups
