module
public import LogicLineages.ModelsAlgebra.PGroups.SocleCorrectionTransportTargets
public import Mathlib.Algebra.Module.Submodule.Equiv
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
universe u

private theorem correction_domain_transport (G H : Type u) [AddCommGroup G] [AddCommGroup H]
    (p : ℕ) (B S : AddSubgroup G) (C T : AddSubgroup H) (f : B ≃+ C)
    (hs : ∀ b : B, (f b:H) ∈ T ↔ (b:G) ∈ S)
    (h2 : ∀ b : B, (f b:H) ∈ pStep p (pStep p T) ↔ (b:G) ∈ pStep p (pStep p S))
    (x : socleCorrectionDomain G p B S) :
    (f ⟨x,x.property.1.1⟩:H) ∈ socleCorrectionDomain H p C T := by
  let b : B := ⟨x,x.property.1.1⟩
  refine ⟨⟨(f b).property,(hs b).mpr x.property.1.2⟩,?_⟩
  have hm := (h2 (p • b)).mpr x.property.2
  change p • (f b:H) ∈ pStep p (pStep p T)
  simpa only [map_nsmul,AddSubgroup.coe_nsmul] using hm

theorem socle_correction_transport : Targets.groupSocleCorrectionTransport.{u} := by
  intro G H _ _ p B S C T f hs h1 h2
  have hs' (c : C) : (f.symm c:G) ∈ S ↔ (c:H) ∈ T := by
    simpa only [f.apply_symm_apply] using (hs (f.symm c)).symm
  have h1' (c : C) : (f.symm c:G) ∈ pStep p S ↔ (c:H) ∈ pStep p T := by
    simpa only [f.apply_symm_apply] using (h1 (f.symm c)).symm
  have h2' (c : C) : (f.symm c:G) ∈ pStep p (pStep p S) ↔ (c:H) ∈ pStep p (pStep p T) := by
    simpa only [f.apply_symm_apply] using (h2 (f.symm c)).symm
  let e : socleCorrectionDomain G p B S ≃+ socleCorrectionDomain H p C T :=
    { toFun := fun x => ⟨f ⟨x,x.property.1.1⟩,correction_domain_transport G H p B S C T f hs h2 x⟩
      invFun := fun y => ⟨f.symm ⟨y,y.property.1.1⟩,correction_domain_transport H G p C T B S f.symm hs' h2' y⟩
      left_inv := by
        intro x
        apply Subtype.ext
        exact congrArg (fun b : B => (b:G)) (f.symm_apply_apply ⟨x,x.property.1.1⟩)
      right_inv := by
        intro y
        apply Subtype.ext
        exact congrArg (fun c : C => (c:H)) (f.apply_symm_apply ⟨y,y.property.1.1⟩)
      map_add' := by
        intro x y
        apply Subtype.ext
        exact congrArg (fun c : C => (c:H)) (map_add f ⟨x,x.property.1.1⟩ ⟨y,y.property.1.1⟩) }
  let NG := (pStep p S).comap (socleCorrectionDomain G p B S).subtype
  let NH := (pStep p T).comap (socleCorrectionDomain H p C T).subtype
  have hn : NG.map e.toAddMonoidHom = NH := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact (h1 ⟨x,x.property.1.1⟩).mpr hx
    · intro hy
      refine ⟨e.symm y,?_,e.apply_symm_apply y⟩
      exact (h1' ⟨y,y.property.1.1⟩).mpr hy
  let eqv := QuotientAddGroup.congr NG NH e hn
  exact ⟨LinearEquiv.ofBijective (eqv.toAddMonoidHom.toZModLinearMap p) eqv.bijective⟩

theorem socle_correction_rank_transport : Targets.groupSocleCorrectionRankTransport.{u} := by
  intro G H _ _ p B S C T f hs h1 h2
  obtain ⟨e⟩ := socle_correction_transport G H p B S C T f hs h1 h2
  exact e.rank_eq

end LogicLineages.ModelsAlgebra.PGroups
