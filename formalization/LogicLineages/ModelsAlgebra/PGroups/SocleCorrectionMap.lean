module
public import LogicLineages.ModelsAlgebra.PGroups.SocleCorrectionMapTargets
public import Mathlib.Tactic.Abel
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
universe u

private theorem representative_difference (G : Type u) [AddCommGroup G] (p : ℕ)
    (B S : AddSubgroup G) (x : socleCorrectionDomain G p B S) :
    (socleCorrectionRepresentative G p B S x : G) - x ∈ pStep p S := by
  let h := socle_correction_representative G p S x x.property.1.2 x.property.2
  have hy := (Classical.choose_spec h).1
  change ((x:G)-Classical.choose h)-(x:G) ∈ pStep p S
  have he : ((x:G)-Classical.choose h)-(x:G) = -Classical.choose h := by abel
  rw [he]
  exact (pStep p S).neg_mem hy

theorem socle_correction_evaluation : Targets.groupSocleCorrectionEvaluation.{u} := by
  intro G _ p B S x a ha
  apply (socle_correction_equality G p S (socleCorrectionRepresentative G p B S x) a).mpr
  have he : (socleCorrectionRepresentative G p B S x:G)-(a:G) =
      ((socleCorrectionRepresentative G p B S x:G)-(x:G))-((a:G)-(x:G)) := by abel
  rw [he]
  exact (pStep p S).sub_mem (representative_difference G p B S x) ha

theorem socle_correction_hom_kernel : Targets.groupSocleCorrectionHomKernel.{u} := by
  intro G _ p B S
  let q := QuotientAddGroup.mk' (successorSocleSubgroup p S)
  let r := socleCorrectionRepresentative G p B S
  have hzero : socleCorrectionClass G p B S 0 = 0 := by
    have he := socle_correction_evaluation G p B S 0 0 (by
      change (0:G)-0 ∈ pStep p S
      simpa only [sub_zero] using (pStep p S).zero_mem)
    simpa only [map_zero] using he
  have hadd (x y : socleCorrectionDomain G p B S) :
      socleCorrectionClass G p B S (x+y) =
        socleCorrectionClass G p B S x + socleCorrectionClass G p B S y := by
    have hd : ((r x + r y : pSocle p S):G) - ((x+y:socleCorrectionDomain G p B S):G) ∈ pStep p S := by
      change (r x:G)+(r y:G)-((x:G)+(y:G)) ∈ pStep p S
      have he : (r x:G)+(r y:G)-((x:G)+(y:G)) =
          ((r x:G)-(x:G))+((r y:G)-(y:G)) := by abel
      rw [he]
      exact (pStep p S).add_mem (representative_difference G p B S x)
        (representative_difference G p B S y)
    rw [socle_correction_evaluation G p B S (x+y) (r x+r y) hd]
    exact map_add q (r x) (r y)
  let f : socleCorrectionDomain G p B S →+ UlmLayer p S :=
    { toFun := socleCorrectionClass G p B S, map_zero' := hzero, map_add' := hadd }
  refine ⟨f,fun _ => rfl,?_⟩
  ext x
  change socleCorrectionClass G p B S x = 0 ↔ (x:G) ∈ pStep p S
  have hq : socleCorrectionClass G p B S x = 0 ↔ (r x:G) ∈ pStep p S := by
    simpa only [map_zero, AddSubgroup.coe_zero, sub_zero, socleCorrectionClass, r] using
      socle_correction_equality G p S (r x) 0
  rw [hq]
  constructor
  · intro hr
    have he : (x:G) = (r x:G)-((r x:G)-(x:G)) := by abel
    rw [he]
    exact (pStep p S).sub_mem hr (representative_difference G p B S x)
  · intro hx
    have he : (r x:G) = ((r x:G)-(x:G))+(x:G) := by abel
    rw [he]
    exact (pStep p S).add_mem (representative_difference G p B S x) hx

end LogicLineages.ModelsAlgebra.PGroups
