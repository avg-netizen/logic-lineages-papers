module
public import LogicLineages.ModelsAlgebra.PGroups.SocleCorrectionCriterionTargets
public import LogicLineages.ModelsAlgebra.PGroups.SocleCorrectionMap
public import Mathlib.Tactic.Abel
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
universe u

private theorem correction_difference (G : Type u) [AddCommGroup G] (p : ℕ)
    (B S : AddSubgroup G) (x : socleCorrectionDomain G p B S) :
    (socleCorrectionRepresentative G p B S x : G) - x ∈ pStep p S := by
  let h := socle_correction_representative G p S x x.property.1.2 x.property.2
  have hy := (Classical.choose_spec h).1
  change ((x:G)-Classical.choose h)-(x:G) ∈ pStep p S
  have he : ((x:G)-Classical.choose h)-(x:G) = -Classical.choose h := by abel
  rw [he]
  exact (pStep p S).neg_mem hy

theorem socle_correction_nonsurjective : Targets.groupSocleCorrectionNonsurjective.{u} := by
  classical
  intro G _ p B S
  constructor
  · intro hn
    change ¬∀ y, ∃ x, socleCorrectionClass G p B S x = y at hn
    push_neg at hn
    obtain ⟨y,hy⟩ := hn
    obtain ⟨a,ha⟩ := QuotientAddGroup.mk'_surjective (successorSocleSubgroup p S) y
    have havoid (b : B) : (a:G)+b ∉ pStep p S := by
      intro hab
      have hbS : (b:G) ∈ S := by
        simpa only [add_sub_cancel_left] using S.sub_mem (pStep_le p S hab) a.property.1
      have hpa : p • (a:G) = 0 := a.property.2
      have hp : p • (-(b:G)) ∈ pStep p (pStep p S) := by
        refine ⟨-((a:G)+(b:G)),(pStep p S).neg_mem hab,?_⟩
        change p • (-((a:G)+(b:G))) = p • (-(b:G))
        simp only [smul_neg,smul_add,hpa,zero_add]
      let x : socleCorrectionDomain G p B S :=
        ⟨-(b:G),⟨⟨B.neg_mem b.property,S.neg_mem hbS⟩,hp⟩⟩
      have hd : (a:G)-(x:G) ∈ pStep p S := by
        change (a:G)-(-(b:G)) ∈ pStep p S
        simpa only [sub_neg_eq_add] using hab
      exact hy x ((socle_correction_evaluation G p B S x a hd).trans ha)
    refine ⟨a,?_,havoid⟩
    simpa only [AddSubgroup.coe_zero,add_zero] using havoid 0
  · rintro ⟨a,ha,havoid⟩ hsurj
    obtain ⟨x,hx⟩ := hsurj ((QuotientAddGroup.mk' (successorSocleSubgroup p S)) a)
    let r := socleCorrectionRepresentative G p B S x
    have hr : (r:G)-(a:G) ∈ pStep p S :=
      (socle_correction_equality G p S r a).mp hx
    have hd := correction_difference G p B S x
    have he : (a:G)-(x:G) = ((r:G)-(x:G))-((r:G)-(a:G)) := by abel
    have ham : (a:G)-(x:G) ∈ pStep p S := by
      rw [he]
      exact (pStep p S).sub_mem hd hr
    apply havoid ⟨-(x:G),B.neg_mem x.property.1.1⟩
    simpa only [sub_eq_add_neg] using ham

end LogicLineages.ModelsAlgebra.PGroups
