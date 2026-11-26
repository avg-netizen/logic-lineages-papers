module
public import LogicLineages.PermittedControl.StandardSeededSystemQueriesProof
public import LogicLineages.PermittedControl.SelectedSeededSystemEmptyProof
@[expose] public section
namespace LogicLineages.PermittedControl.StandardSeededSystem.Proof
open OrdinalComparison Source SelectedSourceDomain SelectedFunctionalDetector Source.AdmissibleSum
open Source.FunctionalHardnessCompletion SignedPair
open SelectedSeededSystem (zeroEquation augmentEmpty)
open SelectedSeededSystem.Proof (empty_satisfiable zero_satisfiable augmentation_satisfiable)

/-- The three satisfiability facts are control-free; every query clause is at Phi. -/
theorem emptySourceCorrespondence : StandardSeededSystem.EmptySourceCorrespondence := by
  refine ⟨augmentation_satisfiable,?_⟩
  intro policy n
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro ρ
    constructor <;> exact StandardFunctionalDetector.Proof.zero_value policy ρ
  · intro h
    exact (queryComplements policy n []).1.mp h (empty_satisfiable n)
  · intro h
    exact (queryComplements policy n []).2.mp h (empty_satisfiable n)
  · intro h
    exact (queryComplements policy n [zeroEquation n]).1.mp h (zero_satisfiable n)
  · intro h
    exact (queryComplements policy n [zeroEquation n]).2.mp h (zero_satisfiable n)

theorem standardSeededSystem : StandardSeededSystem.StandardSeededSystem :=
  ⟨valuationPreservation,systemEquality,queryComplements,successfulQueries,
    levelThreeBounds,emptySourceCorrespondence⟩
end LogicLineages.PermittedControl.StandardSeededSystem.Proof
