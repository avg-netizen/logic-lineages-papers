module

public import LogicLineages.ModelsAlgebra.Forests.RankEmbeddingTargets
public import LogicLineages.ModelsAlgebra.Forests.LeafOrderProof

/-! Lift actual calibrated cluster maps through an actual thickening using
strict-predecessor ranks, preserving and reflecting the original forest order. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.RankEmbeddingProof

open GraphBridge

theorem clusterRankEmbedding : Targets.ClusterRankEmbedding := by
  intro F T H n points q hpoints hq heq hn
  let r (x : F.Carrier) : Fin n :=
    ⟨twinRank F x, lt_of_lt_of_le (LeafOrderProof.twinRankBelowCarrierCard F x) hn⟩
  let f : F.Carrier → H.Carrier := fun x => points (q x, r x)
  have horder (x y : F.Carrier) : f x ≤ f y ↔ x ≤ y := by
    change points (q x, r x) ≤ points (q y, r y) ↔ x ≤ y
    rw [hpoints]
    change (q x ≤ q y ∧ (q x = q y → twinRank F x ≤ twinRank F y)) ↔ x ≤ y
    rw [hq, heq]
    exact (LeafOrderProof.leafClusterRankOrderRecovery F x y).symm
  have hinj : Function.Injective f := by
    intro x y hxy
    exact le_antisymm ((horder x y).mp (le_of_eq hxy))
      ((horder y x).mp (le_of_eq hxy.symm))
  exact ⟨{ toFun := f, inj' := hinj, map_rel_iff' := fun {x y} => horder x y }⟩

end LogicLineages.ModelsAlgebra.Forests.RankEmbeddingProof
