module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityClosureDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityClosureTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationValidityStack
open InternalApplicationValidityStackAppend InternalApplicationValidityClosure
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Acceptance by the actual finished AST is internally equivalent to the
literal original terminal state TWO, on every symbolic raw state. -/
def ActualOriginalFinishedAcceptance : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (state : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body []
    ((graph1 finished InternalOriginalStepGuard.one state).iff
      (equal state successState)))

/-- Acceptance of the frozen validator is exactly singleton success at the
original payload PLUS ONE. The actual right-selector and original list-cons
graphs are the only witnesses; neither count nor fuel is supplied freely. -/
def ActualOriginalValidatorSingletonSuccess : Prop :=
  ∀ (body : Positive (Fin 1)) (node leaf : Program 1) (α : Type)
    (value payload singleton : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body []
    ((graph1 InternalUnpair.right payload value ⊓
      graph2 InternalListCodec.consCode singleton value OrdinaryArithmetic.zeroTerm).imp
      ((graph1 (validator node leaf) InternalOriginalStepGuard.one value).iff
        (successfulWork node leaf (OrdinaryArithmetic.succTerm payload) singleton))))

/-- Genuine internal application closure for arbitrary actual node/leaf ASTs.
The child values have their exact original reconstructed type and payload
graphs. The parent uses the unchanged bounded validator, whose count is its
own payload+1; no larger fuel, size bound, semantic calibration, correctness
field, or assumed application closure occurs in the premises. -/
def ActualOriginalValidatorApplicationClosure : Prop :=
  ∀ (body : Positive (Fin 1)) (node leaf : Program 1) (α : Type)
    (arrow d e fp ap fn arg parent : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body []
    ((applicationConstructors arrow d e fp ap fn arg parent ⊓
      (graph1 node InternalOriginalStepGuard.one e ⊓
        (graph1 (validator node leaf) InternalOriginalStepGuard.one fn ⊓
          graph1 (validator node leaf) InternalOriginalStepGuard.one arg))).imp
      (graph1 (validator node leaf) InternalOriginalStepGuard.one parent)))

/-- Instantiate BOTH branches of the original recursiveData and discharge
the source/target application-validity obligations from the actual endpoint.
The endpoint supplies source, target, argument, membership and all raw tags.
Argument source-to-target comes from the concrete conjunction, not a premise.
No source-universe test is imposed on t or on the target application. -/
def ActualOriginalRecursiveEndpointApplicationValidity : Prop :=
  ∀ (body : Positive (Fin 1)) (old : InternalOriginalStepGuard.Data) (member : Program 1)
    (α : Type) (arrow d e s t a sourceApp targetApp : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body []
    ((endpointApplicationPremises old member arrow d e s t a sourceApp targetApp).imp
      (graph1 (recursiveData old member).sourceValid InternalOriginalStepGuard.one sourceApp ⊓
        graph1 (recursiveData old member).targetValid InternalOriginalStepGuard.one targetApp)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityClosureTargets
