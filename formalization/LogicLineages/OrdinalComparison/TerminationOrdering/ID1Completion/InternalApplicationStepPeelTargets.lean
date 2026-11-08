module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelTargets
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationStepPeel
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- All-input external calibration is separate from the two internal graph
laws below. Rejected, malformed and structurally mismatched states remain in scope. -/
def ActualOriginalTransitionCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (endpoint : Program 5),
  EndpointCalibrated n arity symbols S Gamma endpoint →
  ∀ state : Nat,
    evaluate (guard endpoint) (List.Vector.ofFn ![state]) =
      guardValue n arity symbols S Gamma state ∧
    evaluate (transition endpoint) (List.Vector.ofFn ![state]) =
      transitionValue n arity symbols S Gamma state

/-- A lifted original state peels to EXACTLY the original state at every
output, given its actual endpoint-guard graph and explicit original outer tags.
All natural certificate payloads are retained, including malformed suffixes.
No calibration hypothesis or semantic-to-derivability principle occurs. -/
def ActualOriginalLiftedTransition : Prop :=
  ∀ (body : Positive (Fin 1)) (endpoint : Program 5) (α : Type)
    (d e arrow s t a certificate k lifted out : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body []
    ((taggedEdge d e arrow s t a certificate k ⊓
      (graph5 endpoint (OrdinaryArithmetic.succTerm OrdinaryArithmetic.zeroTerm) d e s t a ⊓
        graph4 edgeLift lifted d e a certificate)).imp
      ((graph1 (transition endpoint) out lifted).iff (equal out certificate))))

/-- Every failed guard, regardless of which original test rejects, keeps
exactly the same raw state. This is full-output graph equivalence, not acceptance. -/
def ActualOriginalRejectedTransition : Prop :=
  ∀ (body : Positive (Fin 1)) (endpoint : Program 5) (α : Type)
    (state out : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body []
    ((graph1 (guard endpoint) OrdinaryArithmetic.zeroTerm state).imp
      ((graph1 (transition endpoint) out state).iff (equal out state))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelTargets
