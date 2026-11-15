module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedLayerCalibration.StatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedStandaloneExtraction.StatementChecks
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedExchangeEquation
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114
/-- The existing literal rank/dependency/graph/head-pair-snd recursor at the
newly calibrated fixed original layer. No existential supplier is selected. -/
def exchange (n : Nat) (arity : Fin n → Nat) : Program 2 :=
  ExchangeSelectedRecursor.exchange (OriginalDecodedRank.rank n)
    (OriginalDecodedDependencies.dependencies n) (OriginalDecodedLayerCalibration.layer n arity)
/-- Auxiliary ordered map step inputs [child,tail answers,parameter]. It
retains every child, duplicate and zero payload. This is not cache filterMap. -/
def answerStep (n : Nat) (arity : Fin n → Nat) : Program 3 :=
  .composition InternalListCodec.consCode
    ![.composition (exchange n arity) ![.projection 0,.projection 2],.projection 1]
def answerMap (n : Nat) (arity : Fin n → Nat) : Program 2 :=
  InternalRawListRecursion.listRec (InternalAcceptance.constantZero 1) (answerStep n arity)
/-- Original ordered D list, unchanged parameter; children evaluated standalone. -/
def answers (n : Nat) (arity : Fin n → Nat) : Program 2 :=
  .composition (answerMap n arity) ![OriginalDecodedDependencies.dependencies n,.projection 1]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedExchangeEquation
