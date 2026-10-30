module
public import LogicLineages.ModelsAlgebra.PGroups.CyclicClassificationTargets
public import LogicLineages.ModelsAlgebra.PGroups.CyclicDecomposition
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

theorem bounded_cyclic_calibrated_decomposition : Targets.groupBoundedCyclicCalibratedDecomposition := by
  classical
  intro p _ G _ N hb
  obtain ⟨I,b,x,y,h⟩ := ulm_basis_lift_existence p G
  let J : Fin N → Type := fun l => I l.val
  let yy : ∀ l : Fin N, J l → G := fun l => y l.val
  have hy : ∀ l i, p ^ (l.val+1) • yy l i = 0 := fun l i => (h l.val i).2.2
  let f := cyclicRootSumHom p N J G yy hy
  have hi : Function.Injective f := cyclic_root_sum_injective p N J G yy hy
    (includedSocleFamily p N J (fun l => x l.val))
    (fun a => (h a.1.val a.2).2.1)
    (adapted_socle_independent p G N J (fun l => b l.val) (fun l => x l.val)
      (fun l i => (h l.val i).1))
  have hs : Function.Surjective f := cyclic_root_sum_surjective p G N hb J
    (fun l => b l.val) (fun l => x l.val) yy hy
    (fun l i => (h l.val i).1) (fun l i => (h l.val i).2.1)
  exact ⟨J, ⟨(AddEquiv.ofBijective f ⟨hi,hs⟩).symm⟩, fun l => (b l.val).mk_eq_rank''⟩


theorem cyclic_root_sum_reindex : Targets.groupCyclicRootSumReindex := by
  classical
  intro p N I J h
  let e : (Σ l : Fin N, I l) ≃ (Σ l : Fin N, J l) :=
    Equiv.sigmaCongrRight (fun l => Classical.choice (h l))
  let q := DFinsupp.equivCongrLeft (β := fun a : Σ l : Fin N, I l => ZMod (p ^ (a.1.val+1))) e
  refine ⟨{ q with map_add' := ?_ }⟩
  intro x y
  ext a
  rfl

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
