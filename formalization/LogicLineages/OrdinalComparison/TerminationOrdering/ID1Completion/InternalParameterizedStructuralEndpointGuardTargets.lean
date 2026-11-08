module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedStructuralEndpointGuardDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedStructuralEndpointGuardTargets
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalParameterizedStructuralEndpointGuard
open InternalOriginalUniformDescentSelection (Data)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The selected endpoint has the exact original all-input endpointValue at
every encoded source window/Gamma. No subtype-closure, valid-input or decoded
term premise is introduced, and the target universe filter stays absent. -/
def ActualOriginalParameterizedStructuralEndpointCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (data : Data),
  InternalOriginalUniformDescentSelection.Calibrated n arity data →
  ∀ (symbols : List (Fin n)) (S Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (v : List.Vector Nat 5),
  evaluate (selectedEndpoint data) (List.Vector.ofFn
    ![v.get 0,v.get 1,v.get 2,v.get 3,v.get 4,
      InternalOriginalUniformParameterLeaves.parameterCode symbols S Gamma table]) =
    InternalApplicationStepPeel.endpointValue n arity symbols S Gamma v

/-- Literal factorization and introduction for arbitrary actual binary
Programs. The original arrow constructor graph alone supplies its code;
all seven accepted factors are derived in the forward implication. -/
def ActualParameterizedEndpointAcceptanceAtArrow : Prop :=
  ∀ (body : Positive (Fin 1)) (sourceValid targetValid member : Program 2)
    (α : Type) (Delta : List (Formula α))
    (arrow d e s t a parameter : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Delta
    ((graph2 InternalListCodec.consCode arrow d e).imp
      ((accepted sourceValid targetValid member d e s t a parameter).iff
        (requirements sourceValid targetValid member arrow d e s t a parameter))))

/-- For the actual recursive validators, endpoint acceptance and original
raw application graphs imply both lifted validity graphs and the exact common
result tag at the SAME symbolic parameter. No calibration premise occurs. -/
def ActualParameterizedEndpointApplicationValidity : Prop :=
  ∀ (body : Positive (Fin 1)) (data : Data) (α : Type) (Delta : List (Formula α))
    (arrow d e s t a sourceApp targetApp parameter : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Delta
    ((applicationPremises data arrow d e s t a sourceApp targetApp parameter).imp
      (applicationValidity data sourceApp targetApp e parameter)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedStructuralEndpointGuardTargets
