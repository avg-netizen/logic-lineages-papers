module
public import LogicLineages.ModelsAlgebra.PGroups.DirectSumFiltrationTargets
public import LogicLineages.ModelsAlgebra.PGroups.TransfiniteFiltration
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
universe u v w

theorem direct_sum_subgroup_coordinates : Targets.directSumSubgroupCoordinates.{u,v} := by
  classical
  intro ι G _ S x
  constructor
  · rintro ⟨y, rfl⟩ i
    exact (y i).property
  · intro hx
    let y : DirectSum ι (fun i => S i) :=
      DFinsupp.mk (DFinsupp.support x) (fun i => ⟨x i, hx i⟩)
    refine ⟨y, ?_⟩
    apply DirectSum.ext
    intro i
    rw [DirectSum.map_apply]
    change (y i).val = x i
    by_cases hi : i ∈ DFinsupp.support x
    · simp [y, DFinsupp.mk_apply, hi]
    · have hz : x i = 0 := DFinsupp.notMem_support_iff.mp hi
      simp [y, DFinsupp.mk_apply, hi, hz]

private theorem direct_sum_step {ι : Type u} {G : ι → Type v}
    [∀ i, AddCommGroup (G i)] (p : ℕ) (S : ∀ i, AddSubgroup (G i)) :
    pStep p (directSumSubgroup S) = directSumSubgroup (fun i => pStep p (S i)) := by
  classical
  ext x
  rw [direct_sum_subgroup_coordinates]
  constructor
  · rintro ⟨y, hy, rfl⟩ i
    exact ⟨y i, (direct_sum_subgroup_coordinates S y).mp hy i, rfl⟩
  · intro hx
    choose y hy heq using hx
    let z : DirectSum ι G := DFinsupp.mk (DFinsupp.support x) (fun i => y i)
    refine ⟨z, (direct_sum_subgroup_coordinates S z).mpr ?_, ?_⟩
    · intro i
      change (DFinsupp.mk (DFinsupp.support x) (fun i => y i)) i ∈ S i
      by_cases hi : i ∈ DFinsupp.support x
      · simpa [DFinsupp.mk_apply, hi] using hy i
      · simp [DFinsupp.mk_apply, hi]
    · apply DirectSum.ext
      intro i
      change p • (DFinsupp.mk (DFinsupp.support x) (fun i => y i)) i = x i
      by_cases hi : i ∈ DFinsupp.support x
      · simpa [DFinsupp.mk_apply, hi] using heq i
      · have hz : x i = 0 := DFinsupp.notMem_support_iff.mp hi
        simp [DFinsupp.mk_apply, hi, hz]

theorem transfinite_direct_sum : Targets.transfiniteDirectSum.{u,v,w} := by
  intro ι G _ p α
  refine Ordinal.limitRecOn α ?_ (fun β ih => ?_) (fun β hβ ih => ?_)
  · simp only [transfiniteFiltration_zero]
    ext x
    rw [direct_sum_subgroup_coordinates]
    simp
  · rw [transfiniteFiltration_add_one, ih, direct_sum_step]
    congr 1
    funext i
    exact (transfiniteFiltration_add_one p β).symm
  · ext x
    rw [transfiniteFiltration_limit p hβ, direct_sum_subgroup_coordinates]
    simp only [AddSubgroup.mem_iInf]
    constructor
    · intro hx i
      rw [transfiniteFiltration_limit p hβ]
      exact AddSubgroup.mem_iInf.mpr (fun γ =>
        (direct_sum_subgroup_coordinates _ x).mp (ih γ.1 γ.2 ▸ hx γ) i)
    · intro hx γ
      rw [ih γ.1 γ.2, direct_sum_subgroup_coordinates]
      intro i
      have hi := hx i
      rw [transfiniteFiltration_limit p hβ] at hi
      exact AddSubgroup.mem_iInf.mp hi γ
end LogicLineages.ModelsAlgebra.PGroups
