module
public import LogicLineages.OrdinalComparison.ActualHeadGraphFormulaTargets
public import LogicLineages.OrdinalComparison.ActualHeadGraphFormulaTailProof
public import LogicLineages.OrdinalComparison.ActualHeadGraphArithmeticProof
public import LogicLineages.OrdinalComparison.ActualUnaryRayProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ActualHeadGraph.FormulaConstruction.Proof
open ForwardTranslation Arithmetic

theorem exactFinitePrefix : Targets.ExactFinitePrefix := by
  intro a c δ t y ν
  rw [finitePrefix,Arithmetic.Proof.disjunction_eval]
  simp only [List.mem_map,List.mem_filter,List.mem_range,decide_eq_true_eq]
  constructor
  · rintro ⟨p,⟨j,⟨hj,hg⟩,rfl⟩,he,hy⟩
    change t.value ν = j at he
    change y.value ν = actualHeadValue (shiftedHead a δ) j at hy
    rw [he]
    exact ⟨hg,hj,hy⟩
  · rintro ⟨hg,hj,hy⟩
    refine ⟨_,⟨t.value ν,⟨hj,hg⟩,rfl⟩,?_⟩
    exact ⟨rfl,hy⟩

theorem actualWholeGenuineGraph : Targets.ActualWholeGenuineGraph := by
  intro Γ K
  obtain ⟨u,a,c,q,hconst,hbuild,hground,hray⟩ := ActualUnaryRay.Proof.actualRayObservation Γ K
  refine ⟨u,a,c,q,hconst,hbuild,hground,?_⟩
  intro δ t y ν
  rw [graph,Formula.eval,exactFinitePrefix,
    exactTailFromRay Γ (UnitElimination.realize q) a c hray]
  constructor
  · rintro (⟨hg,hlt,hy⟩ | ⟨ht,hy⟩)
    · exact ⟨hg,hy⟩
    · have hN : actualOrdinalNorm (shiftedHead a δ) ≤ threshold a c δ := Nat.le_max_left _ _
      exact ⟨hN.trans ht,hy⟩
  · rintro ⟨hg,hy⟩
    by_cases hlt : t.value ν < threshold a c δ
    · exact Or.inl ⟨hg,hlt,hy⟩
    · exact Or.inr ⟨Nat.le_of_not_gt hlt,hy⟩
end LogicLineages.OrdinalComparison.Source.ActualHeadGraph.FormulaConstruction.Proof
