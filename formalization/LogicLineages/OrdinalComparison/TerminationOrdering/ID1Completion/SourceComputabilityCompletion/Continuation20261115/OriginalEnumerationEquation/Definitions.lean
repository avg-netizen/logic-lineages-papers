module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationCacheCoherence.StatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursion.StatementChecks
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationEquation
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114
/-- Ordered raw-list map of THIS literal standalone enumeration. Every child,
duplicate, and zero payload is retained; this is not cache filterMap. -/
def answerStep (n : Nat) : Program 3 :=
  .composition InternalListCodec.consCode
    ![.composition (OriginalEnumerationRecursion.enumeration n)
      ![.projection 0,.projection 2],.projection 1]
def answerMap (n : Nat) : Program 2 :=
  InternalRawListRecursion.listRec (InternalAcceptance.constantZero 1) (answerStep n)
/-- The unchanged original ordered two-child D (or empty at fuel zero). -/
def answers (n : Nat) : Program 2 :=
  .composition (answerMap n) ![OriginalEnumerationRecursionInterface.D,.projection 1]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationEquation
