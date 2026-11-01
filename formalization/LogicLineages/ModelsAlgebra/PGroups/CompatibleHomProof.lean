module
public import LogicLineages.ModelsAlgebra.PGroups.CompatibleHomTargets
public import LogicLineages.ModelsAlgebra.PGroups.DivisibleExtensionProof
public import Mathlib.GroupTheory.QuotientGroup.Basic
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

theorem compatible_divisible_hom_extension : Targets.compatibleDivisibleHomExtension := by
  classical
  intro G E _ _ hdiv B S f u hcompatible
  obtain ⟨F₀,hF₀⟩ := divisible_hom_extension G E hdiv B f
  let q : G →+ G ⧸ B := QuotientAddGroup.mk' B
  let v : S →+ G ⧸ B := q.comp S.subtype
  let d : S →+ E := u-F₀.comp S.subtype
  have hker : v.ker ≤ d.ker := by
    intro x hx
    have hxB : (x:G) ∈ B :=
      (QuotientAddGroup.eq_zero_iff _).mp (show q (x:G)=0 from hx)
    change u x-F₀ (x:G)=0
    rw [←hcompatible (x:G) hxB x.property,hF₀ ⟨x,hxB⟩,sub_self]
  let dbar : (S ⧸ v.ker) →+ E := QuotientAddGroup.lift v.ker d hker
  let e : (S ⧸ v.ker) ≃+ v.range := QuotientAddGroup.quotientKerEquivRange v
  let w : v.range →+ E := dbar.comp e.symm.toAddMonoidHom
  have hw (x:S) : w (v.rangeRestrict x)=d x := by
    have he : e (QuotientAddGroup.mk x)=v.rangeRestrict x := rfl
    rw [←he]
    change dbar (e.symm (e (QuotientAddGroup.mk x)))=d x
    rw [e.symm_apply_apply]
    rfl
  obtain ⟨a,ha⟩ := divisible_hom_extension (G ⧸ B) E hdiv v.range w
  refine ⟨F₀+a.comp q,?_,?_⟩
  · intro x
    change F₀ (x:G)+a (q (x:G))=f x
    have hq : q (x:G)=0 := (QuotientAddGroup.eq_zero_iff _).mpr x.property
    rw [hq,map_zero,add_zero,hF₀]
  · intro x
    change F₀ (x:G)+a (v x)=u x
    have hax : a (v x)=d x := (ha (v.rangeRestrict x)).trans (hw x)
    rw [hax]
    change F₀ (x:G)+(u x-F₀ (x:G))=u x
    rw [add_comm (F₀ (x:G)),sub_add_cancel]

end LogicLineages.ModelsAlgebra.PGroups
