module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationStepCheckerDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedStructuralEndpointGuardDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformApplicationStepSelection
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalOriginalUniformDescentSelection (Data)
open InternalOriginalUniformParameterLeaves (parameterCode parameterObject)
open InternalParameterizedApplicationStepChecker
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Inputs [source,target,originalStepCertificate,parameter]. Decode the
original context and Object, with the raw source in its unchanged second
coordinate. A malformed context returns zero. No window or Gamma is fixed. -/
def leafValue (n : Nat) (arity : Fin n → Nat) (v : List.Vector Nat 4) : Nat :=
  match Encodable.decode (α := OrdinaryArithmeticQuotient.Context n) (Nat.unpair (v.get 3)).1,
      parameterObject (v.get 0) (v.get 3) with
  | some ctx, some obj =>
    (NumberedNumericStep.numericStepTest n arity ctx.1.1 ctx.1.2 obj.1 ctx.2
      obj.2 (v.get 1) (v.get 2)).toNat
  | _, _ => 0

def LeafCalibrated (n : Nat) (arity : Fin n → Nat) (oldStep : Program 4) : Prop :=
  ∀ v : List.Vector Nat 4, evaluate oldStep v = leafValue n arity v

/-- The concrete parameterized peel-and-repeat program, with the actual
selected seven-test endpoint. The old step leaf is selected globally. -/
def selectedChecker (data : Data) (oldStep : Program 4) : Program 4 :=
  checkerP (InternalParameterizedStructuralEndpointGuard.selectedEndpoint data) oldStep

def SelectedCalibrated (n : Nat) (arity : Fin n → Nat) (data : Data) (oldStep : Program 4) : Prop :=
  ∀ (symbols : List (Fin n)) (S Gamma : List Ty) (table : Fin n → Fin n → Bool),
    StepCalibratedAt n arity symbols S Gamma table (selectedChecker data oldStep)
      (parameterCode symbols S Gamma table)

/-- The actual selected endpoint and actual checker satisfy the original
application-step equation at an arbitrary symbolic parameter. This contains
only the local raw constructor and endpoint premises from the source rule. -/
def InternalLaw (data : Data) (oldStep : Program 4) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Delta : List (Formula α))
    (d e arrow s t a certificate sourceApp targetApp lifted out parameter : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Delta
    ((liftedCheckerPremises (InternalParameterizedStructuralEndpointGuard.selectedEndpoint data)
        d e arrow s t a certificate sourceApp targetApp lifted parameter).imp
      ((checkerGraph (InternalParameterizedStructuralEndpointGuard.selectedEndpoint data) oldStep
          out sourceApp targetApp lifted parameter).iff
        (checkerGraph (InternalParameterizedStructuralEndpointGuard.selectedEndpoint data) oldStep
          out s t certificate parameter))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformApplicationStepSelection
