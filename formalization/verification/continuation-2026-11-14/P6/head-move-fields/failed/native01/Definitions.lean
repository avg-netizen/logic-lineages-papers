module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadMove.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ResultStructuralFields.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadMoveFields
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalRawSyntaxTransport InternalApplicationCertificateConstructors
/-- Raw window parameter is the original Encodable product of symbol/type lists. -/
def symbols : Program 3 := leftOf (.projection 2)
def types : Program 3 := rightOf (.projection 2)
def body (n : Nat) (arity : Fin n → Nat) (V : Program 3) : Program 3 :=
  .composition (OriginalHeadMove.headMove n arity)
    ![TransparentMetadataFields.head V false,TransparentChildFields.first V false,
      TransparentMetadataFields.head V true,TransparentChildFields.first V true,symbols,types]
/-- Invalid original node/window still produces the exact zero field default. -/
def move (n : Nat) (arity : Fin n → Nat) (V : Program 3) : Program 3 :=
  InternalAcceptance.branch V (constant 3 0) (body n arity V)
def suppliers (n : Nat) (arity : Fin n → Nat) (U : Fin 19 → Program 3) (V : Program 3) (i : Fin 19) : Program 3 :=
  if i = 16 then move n arity V else U i
def fields (n : Nat) (arity : Fin n → Nat) (U : Fin 19 → Program 3) (V : Program 3) : Fin 19 → Program 3 :=
  ResultStructuralFields.fields (suppliers n arity U V) V
def layer (n : Nat) (arity : Fin n → Nat) (U : Fin 19 → Program 3) (V : Program 3) : Program 3 :=
  ResultStructuralFields.layer (suppliers n arity U V) V

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadMoveFields
