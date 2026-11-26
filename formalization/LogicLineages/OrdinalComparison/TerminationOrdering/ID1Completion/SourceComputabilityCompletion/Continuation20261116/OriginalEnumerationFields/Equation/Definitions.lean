module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.CacheCoherence.Proof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Equation
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Ordered map step [child,tail answers,parameter]. This retains every child
and zero payload, without the cache filterMap's Option omission. -/
def answerStep (n : Nat) : Program 3 := .composition InternalListCodec.consCode
  ![.composition (OriginalEnumerationFields.extract n) ![.projection 0,.projection 2],.projection 1]
def answerMap (n : Nat) : Program 2 :=
  InternalRawListRecursion.listRec (InternalAcceptance.constantZero 1) (answerStep n)
def answers (n : Nat) : Program 2 := .composition (answerMap n)
  ![OriginalEnumerationFields.dependency,.projection 1]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Equation
