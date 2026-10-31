module
public import LogicLineages.ModelsAlgebra.PGroups.WalkerPresentedTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

private theorem map_parent {V K : Type} [AddCommGroup K] (f : FreeAbelianGroup V →+ K)
    (o : Option V) : f (o.elim 0 FreeAbelianGroup.of) = o.elim 0 (fun v => f (FreeAbelianGroup.of v)) := by
  cases o <;> simp

theorem walker_presented_relations : Targets.walkerPresentedRelations := by
  intro V p parent v
  let q := QuotientAddGroup.mk' (walkerPresentationRelations p parent)
  have hm : walkerPresentationRelation p parent v ∈ walkerPresentationRelations p parent :=
    AddSubgroup.subset_closure ⟨v, rfl⟩
  have hz : q (walkerPresentationRelation p parent v) = 0 :=
    (QuotientAddGroup.eq_zero_iff _).mpr hm
  change q (p • FreeAbelianGroup.of v - (parent v).elim 0 FreeAbelianGroup.of) = 0 at hz
  rw [map_sub, map_nsmul, map_parent] at hz
  exact sub_eq_zero.mp hz

theorem walker_presented_hom_ext : Targets.walkerPresentedHomExt := by
  intro V p parent K _ f g h
  let q := QuotientAddGroup.mk' (walkerPresentationRelations p parent)
  have he : f.comp q = g.comp q := FreeAbelianGroup.lift_ext _ _ h
  apply AddMonoidHom.ext
  intro x
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective (walkerPresentationRelations p parent) x
  exact congrArg (fun k => k a) he

theorem walker_presented_universal : Targets.walkerPresentedUniversal := by
  intro V p parent K _ y hy
  let φ := FreeAbelianGroup.lift y
  have hk : walkerPresentationRelations p parent ≤ φ.ker := by
    apply (AddSubgroup.closure_le φ.ker).mpr
    rintro _ ⟨v, rfl⟩
    change φ (p • FreeAbelianGroup.of v - (parent v).elim 0 FreeAbelianGroup.of) = 0
    rw [map_sub, map_nsmul, map_parent]
    simp only [φ, FreeAbelianGroup.lift_apply_of]
    rw [hy v, sub_self]
  let f := QuotientAddGroup.lift (walkerPresentationRelations p parent) φ hk
  have hf (v : V) : f (walkerPresentedGenerator p parent v) = y v :=
    FreeAbelianGroup.lift_apply_of y v
  refine ⟨f, hf, ?_⟩
  intro g hg
  exact walker_presented_hom_ext V p parent K g f (fun v => (hg v).trans (hf v).symm)

end LogicLineages.ModelsAlgebra.PGroups
