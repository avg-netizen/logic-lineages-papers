module
public import LogicLineages.PermittedControl.SelectedSeededSystemQueriesProof
@[expose] public section
namespace LogicLineages.PermittedControl.SelectedSeededSystem.Proof
open OrdinalComparison Source SelectedSourceDomain SelectedFunctionalDetector Source.AdmissibleSum
open Source.FunctionalHardnessCompletion SignedPair

 theorem empty_satisfiable (n : Nat) : PolynomialSatisfiable ([] : System n) :=
  ⟨fun _ => 0, fun _ h => False.elim (List.not_mem_nil h)⟩

 theorem zero_satisfiable (n : Nat) : PolynomialSatisfiable [zeroEquation n] := by
  refine ⟨fun _ => 0,?_⟩
  intro d hd
  have he : d=zeroEquation n := List.mem_singleton.mp hd
  subst d
  simp [zeroEquation,polynomialMeaning]

 theorem augmentation_satisfiable (n : Nat) (s : System n) :
    PolynomialSatisfiable (augmentEmpty s) ↔ PolynomialSatisfiable s := by
  cases s with
  | nil => exact iff_of_true (zero_satisfiable n) (empty_satisfiable n)
  | cons d ds => rfl

 theorem emptySourceCorrespondence : SelectedSeededSystemTargets.EmptySourceCorrespondence := by
  refine ⟨augmentation_satisfiable,?_⟩
  intro ctrl K hc policy n
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro ρ
    constructor <;> exact SelectedFunctionalDetector.Proof.zero_value ctrl K hc policy ρ
  · intro h
    exact (queryComplements ctrl K hc policy n []).1.mp h (empty_satisfiable n)
  · intro h
    exact (queryComplements ctrl K hc policy n []).2.mp h (empty_satisfiable n)
  · intro h
    exact (queryComplements ctrl K hc policy n [zeroEquation n]).1.mp h (zero_satisfiable n)
  · intro h
    exact (queryComplements ctrl K hc policy n [zeroEquation n]).2.mp h (zero_satisfiable n)

 theorem selectedSeededSystem : SelectedSeededSystemTargets.SelectedSeededSystem :=
  ⟨valuationPreservingSystem,systemEquality,queryComplements,successfulQueries,
    levelThreeBounds,emptySourceCorrespondence⟩
end LogicLineages.PermittedControl.SelectedSeededSystem.Proof
