module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityCalibrationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityCalibrationTargets
open Source InternalApplicationValidityStack InternalApplicationValidityCalibration
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Every count, status, original list, and arbitrary Program leaf. This matches
the already frozen iterate AST with the external structured execution exactly. -/
def ActualOriginalEncodedStackIteration : Prop :=
  ∀ (node leaf : Program 1) (count : Nat) (state : State),
  evaluate (iterate node leaf) (List.Vector.ofFn ![count, encodeState state]) =
    encodeState (stateIterate
      (fun value => evaluate node (List.Vector.ofFn ![value]))
      (fun value => evaluate leaf (List.Vector.ofFn ![value])) count state)

/-- The unchanged payload sum is sufficient on live states, including a live
empty initial state at count zero. One extra transition covers EVERY initial
status. Both canonical terminal states remain fixed for every further count.
No validity or successful decoding assumption appears in this target. -/
def ActualOriginalStackSufficientFuel : Prop :=
  ∀ (node leaf : Nat → Nat) (state : State) (count : Nat),
  (state.status = 1 → workWeight state.work ≤ count →
    terminal (stateIterate node leaf count state)) ∧
  (workWeight state.work + 1 ≤ count →
    terminal (stateIterate node leaf count state)) ∧
  (terminal state → stateIterate node leaf count state = state)

/-- Both EXISTING complete bounded validators agree with the original tests
on every numeric input vector. Source has exactly its old universe filter;
target has none. Leaf and membership calibration are the only hypotheses. -/
def ActualOriginalBoundedValidatorCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (old : InternalOriginalStepGuard.Data) (member : Program 1),
  InternalOriginalStepGuard.Calibrated n arity symbols S Gamma old →
  InternalStructuralEndpointGuard.MembershipCalibrated S member →
  (∀ v : List.Vector Nat 1,
    evaluate (validator (InternalLessThan.constantOne 1) old.targetValid) v =
      InternalOriginalStepGuard.targetValidityValue n arity Gamma (v.get 0)) ∧
  (∀ v : List.Vector Nat 1,
    evaluate (validator member old.sourceValid) v =
      InternalOriginalStepGuard.sourceValidityValue n arity symbols S Gamma (v.get 0))

/-- The unchanged recursiveData itself satisfies the ORIGINAL full all-input
calibration contract. Its source conjunction is discharged using original
source-implies-target, not by adding target-universe validity or a new premise.
This remains external semantic calibration, not internal constructor closure. -/
def ActualOriginalRecursiveValidityCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (old : InternalOriginalStepGuard.Data) (member : Program 1),
  InternalOriginalStepGuard.Calibrated n arity symbols S Gamma old →
  InternalStructuralEndpointGuard.MembershipCalibrated S member →
  InternalOriginalStepGuard.Calibrated n arity symbols S Gamma (recursiveData old member)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityCalibrationTargets
