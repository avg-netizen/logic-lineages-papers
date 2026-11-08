module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationStepCheckerDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationStepCheckerTargets
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalParameterizedApplicationStepChecker
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- One original raw list cell can perform the binary transition first.
Every state, output, code, head and parameter is symbolic; no decoder,
validity, fuel, termination or calibration assumption is supplied. -/
def ActualParameterizedRawListRepeatFrontCons : Prop :=
  ∀ (body : Positive (Fin 1)) (transition : Program 2) (α : Type)
    (Delta : List (Formula α))
    (code head tail out initial next parameter : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Delta
    ((graph2 InternalListCodec.consCode code head tail ⊓
      graph2 transition next initial parameter).imp
      ((repeatGraph transition out code initial parameter).iff
        (repeatGraph transition out tail next parameter))))

/-- The exact original lifted state peels to the original raw state at the
unchanged symbolic parameter. All original certificate suffixes are included.
The endpoint is an arbitrary actual Program6; no calibration is assumed. -/
def ActualParameterizedOriginalLiftedTransition : Prop :=
  ∀ (body : Positive (Fin 1)) (endpoint : Program 6) (α : Type)
    (Delta : List (Formula α))
    (d e arrow s t a certificate k lifted out parameter : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Delta
    ((InternalApplicationStepPeel.taggedEdge d e arrow s t a certificate k ⊓
      (endpointGraph endpoint InternalOriginalStepGuard.one d e s t a parameter ⊓
        graph4 edgeLift lifted d e a certificate)).imp
      ((transitionGraph endpoint out lifted parameter).iff (equal out certificate))))

/-- Full-output equivalence at original and lifted triples for the SAME
concrete normalized checker, not only preservation of output one. All original
constructor and tag graphs are explicit; parameter and output are arbitrary.
Neither endpoint nor old checker has a semantic hypothesis in this rule. -/
def ActualParameterizedOriginalLiftedChecker : Prop :=
  ∀ (body : Positive (Fin 1)) (endpoint : Program 6) (oldChecker : Program 4)
    (α : Type) (Delta : List (Formula α))
    (d e arrow s t a k sourceApp targetApp liftedStep out parameter : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Delta
    ((liftedCheckerPremises endpoint d e arrow s t a k sourceApp targetApp liftedStep parameter).imp
      ((checkerGraph endpoint oldChecker out sourceApp targetApp liftedStep parameter).iff
        (checkerGraph endpoint oldChecker out s t k parameter))))

/-- All-input calibration to the ORIGINAL numericStepTest at a calibrated
parameter slice. No source-validity, successful decode, valid certificate,
subtype closure, paired parameter or successful transition premise occurs. -/
def ActualParameterizedOriginalCheckerCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (endpoint : Program 6) (oldChecker : Program 4) (parameter : Nat),
  EndpointCalibratedAt n arity symbols S Gamma endpoint parameter →
  StepCalibratedAt n arity symbols S Gamma table oldChecker parameter →
  ∀ v : List.Vector Nat 3,
    evaluate (checkerP endpoint oldChecker)
      (List.Vector.ofFn ![v.get 0,v.get 1,v.get 2,parameter]) =
      (NumberedNumericStep.numericStepTest n arity symbols S Gamma table
        (v.get 0) (v.get 1) (v.get 2)).toNat

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationStepCheckerTargets
