module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ContextUniformPrimaryDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedExchangeCodeDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniformPackedDecodingDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ErasureOrderObstruction
open Source NumberedAuxiliaryCoding NumberedUniformPackedDecoding
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

def arity : Fin 1 → Nat := fun _ => 2
def arguments (first second : Code (Fin 1)) : Code (Fin 1) :=
  .argumentsCons .ground first (.argumentsCons .ground second .argumentsNil)
def lower : Code (Fin 1) := .ordinary (.ranked 0) (arguments (.var 1) (.var 0))
def upper : Code (Fin 1) := .ordinary (.ranked 0) (arguments (.var 0) (.var 1))
def erase (q : Code (Fin 1)) : Code (Fin 1) := OriginalRawSyntaxTransport.eraseCode .ground 0 q

/-- Actual original typed exchange candidates, before and after deleting the
first ground context cell. This is a semantic code theorem, not an internal
graph reflection or a counterexample to any already accepted theorem. -/
def ActualTypedExchangePair : Prop :=
  rawStructuralDecode arity [.ground,.ground] (.ground,lower) = some (.ground,lower) ∧
  rawStructuralDecode arity [.ground,.ground] (.ground,upper) = some (.ground,upper) ∧
  rawStructuralDecode arity [.ground] (.ground,erase lower) = some (.ground,erase lower) ∧
  rawStructuralDecode arity [.ground] (.ground,erase upper) = some (.ground,erase upper) ∧
  NumberedExchangeCode.packedCodeExchange arity [0] [.ground] (.ground,lower) (.ground,upper) = true ∧
  NumberedExchangeCode.packedCodeExchange arity [0] [.ground] (.ground,erase lower) (.ground,erase upper) = true ∧
  evaluate OriginalRawSyntaxTransport.erasePackedRaw
    (List.Vector.ofFn ![0,0,ContextUniformPrimary.packedNumber (.ground,lower)]) =
      ContextUniformPrimary.packedNumber (.ground,erase lower) ∧
  evaluate OriginalRawSyntaxTransport.erasePackedRaw
    (List.Vector.ofFn ![0,0,ContextUniformPrimary.packedNumber (.ground,upper)]) =
      ContextUniformPrimary.packedNumber (.ground,erase upper)

/-- Original numeric candidate order reverses under actual erasure, even
inside one typed exchange class. This refutes an order-preservation premise
for naive least-hit transport; it does NOT assert final-fold noncommutation. -/
def ActualOrderReversal : Prop :=
  ContextUniformPrimary.packedNumber (.ground,lower) < ContextUniformPrimary.packedNumber (.ground,upper) ∧
  ContextUniformPrimary.packedNumber (.ground,erase upper) < ContextUniformPrimary.packedNumber (.ground,erase lower)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ErasureOrderObstruction
