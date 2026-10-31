module
public import LogicLineages.ModelsAlgebra.PGroups.SubgroupSumProductTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

theorem subgroup_sum_product : Targets.subgroupSumProduct := by
  intro G _ S K T hs hd
  let f : (K × T) →+ S :=
    { toFun := fun z => ⟨(z.1:G)+z.2,hs.symm ▸ AddSubgroup.add_mem_sup z.1.property z.2.property⟩
      map_zero' := Subtype.ext (zero_add 0)
      map_add' := fun x y => Subtype.ext (add_add_add_comm _ _ _ _) }
  have hf : Function.Injective f := by
    apply f.ker_eq_bot_iff.mp
    apply le_antisymm _ bot_le
    intro z hz
    have hv : (z.1:G)+(z.2:G)=0 := congrArg (fun w : S => (w:G)) hz
    have ht : (z.1:G) ∈ T := by
      rw [eq_neg_of_add_eq_zero_left hv]
      exact T.neg_mem z.2.property
    have h1 : (z.1:G)=0 := AddSubgroup.disjoint_def.mp hd z.1.property ht
    have h2 : (z.2:G)=0 := by simpa only [h1,zero_add] using hv
    exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
  have hsur : Function.Surjective f := by
    intro z
    have hz : (z:G) ∈ K ⊔ T := by rw [← hs]; exact z.property
    obtain ⟨a,ha,b,hb,hab⟩ := AddSubgroup.mem_sup.mp hz
    exact ⟨(⟨a,ha⟩,⟨b,hb⟩),Subtype.ext hab⟩
  exact ⟨AddEquiv.ofBijective f ⟨hf,hsur⟩,fun _ _ => rfl⟩
end LogicLineages.ModelsAlgebra.PGroups
