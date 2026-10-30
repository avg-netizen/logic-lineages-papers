module

public import LogicLineages.ModelsAlgebra.Forests.CotreeContractionTargets
public import LogicLineages.ModelsAlgebra.Forests.CotreeCounterexampleProof

/-! A concrete parent-label quotient creates the I3 cotree from the cotree of
K1 disjoint union K2, but the corresponding graph embedding is impossible.
This addresses only the explicitly stated unrestricted-contraction reading. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.CotreeContractionProof

open CotreeCounterexample CotreeCounterexampleProof

private instance {n} (T : CotreeData n) (x y z) : Decidable (IsLCA T x y z) := by
  unfold IsLCA
  infer_instance

private instance {n} (T : CotreeData n) : DecidableRel (joinLCA T) := by
  intro x y
  unfold joinLCA
  infer_instance

theorem contractionCotreeValid : Targets.ContractionCotreeValid := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold ValidCotree
    decide +kernel
  · intro x y
    fin_cases x <;> fin_cases y <;> unfold ExistsUnique <;> decide +kernel
  · unfold Function.Injective
    decide +kernel
  · decide +kernel

theorem contractionCotreeGraphExact : Targets.ContractionCotreeGraphExact := by
  constructor
  · ext i j
    simp only [evaluatedGraph, isolatedEdgeGraph, SimpleGraph.fromRel_adj]
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j
    simp only [evaluatedGraph, SimpleGraph.fromRel_adj]
    fin_cases i <;> fin_cases j <;> decide +kernel

theorem concreteParentLabelContraction : Targets.ConcreteParentLabelContraction := by
  unfold Targets.ConcreteParentLabelContraction ParentLabelContraction Function.Surjective
  decide +kernel

theorem contractionGraphNonembedding : Targets.ContractionGraphNonembedding := by
  unfold Targets.ContractionGraphNonembedding
  rw [concreteCotreeGraphsExact.1, contractionCotreeGraphExact.1]
  rintro ⟨e⟩
  have hs : Function.Surjective e :=
    ((Fintype.bijective_iff_injective_and_card e).mpr ⟨e.injective, rfl⟩).2
  obtain ⟨x, hx⟩ := hs 1
  obtain ⟨y, hy⟩ := hs 2
  have hadj : isolatedEdgeGraph.Adj (e x) (e y) := by
    rw [hx, hy]
    simp [isolatedEdgeGraph, SimpleGraph.fromRel_adj]
  have hfalse := e.map_rel_iff.mp hadj
  exact (show ¬ (⊥ : SimpleGraph (Fin 3)).Adj x y by simp) hfalse

theorem literalContractionTransferCounterexample : Targets.LiteralContractionTransferCounterexample := by
  exact ⟨contractionCotreeValid.1, concreteCotreesValid.1,
    concreteParentLabelContraction, contractionGraphNonembedding⟩

end LogicLineages.ModelsAlgebra.Forests.CotreeContractionProof
