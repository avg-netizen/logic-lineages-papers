module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.TwoSol20261113.CalibratedPrimary.MembershipDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Inputs [head,tail-result,candidate,parameter]. Exact-one E acceptance
selects one; otherwise retain the actual tail result. -/
def anyStep (E : Program 3) : Program 4 :=
  InternalAcceptance.branch
    (InternalAcceptance.normalize (.composition E ![.projection 0,.projection 2,.projection 3]))
    (.projection 1) (InternalLessThan.constantOne 4)
/-- Inputs [reached,candidate,parameter], right fold over original reached. -/
def anyEdge (E : Program 3) : Program 3 :=
  InternalRawListRecursion.listRec (InternalAcceptance.constantZero 2) (anyStep E)
/-- Inputs [candidate,tail-result,reached,parameter]. The same reached list is
used at every pool entry, never the newly growing output. -/
def filterStep (E : Program 3) : Program 4 :=
  InternalAcceptance.branch
    (InternalAcceptance.normalize (.composition (anyEdge E)
      ![.projection 2,.projection 0,.projection 3]))
    (.projection 1)
    (.composition InternalListCodec.consCode ![.projection 0,.projection 1])
/-- Inputs [pool,reached,parameter]; original pool order and repeats retained. -/
def filterReached (E : Program 3) : Program 3 :=
  InternalRawListRecursion.listRec (InternalAcceptance.constantZero 2) (filterStep E)
/-- The ORIGINAL one-step order: reached ++ filtered pool. -/
def expand (E : Program 3) : Program 3 :=
  .composition InternalApplicationValidityStackAppend.append
    ![.projection 1,filterReached E]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansion
