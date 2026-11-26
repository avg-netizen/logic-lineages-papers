module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalFixedWindowVertexDispatchDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedExchangeGuardsPrimrecProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHeadClassNumber
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Original heads are pair(tag,payload), not successor-pairs. This key ignores
result/base types. It is not a validity checker: unknown tags return zero,
and unchecked tag-5 payloads return payload+2. No runtime tuple is changed. -/
def tagIs (n : Nat) : Program 1 :=
  .composition InternalEqualityTest.equalityTest
    ![InternalUnpair.left,InternalCanonicalFixedWindowVertexDispatch.constant 1 n]
def classNumber : Program 1 :=
  InternalAcceptance.branch (tagIs 4)
    (InternalAcceptance.branch (tagIs 5) (InternalAcceptance.constantZero 1)
      (.composition .succ (fun _ : Fin 1 => .composition .succ (fun _ : Fin 1 => InternalUnpair.right))))
    (InternalLessThan.constantOne 1)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHeadClassNumber
