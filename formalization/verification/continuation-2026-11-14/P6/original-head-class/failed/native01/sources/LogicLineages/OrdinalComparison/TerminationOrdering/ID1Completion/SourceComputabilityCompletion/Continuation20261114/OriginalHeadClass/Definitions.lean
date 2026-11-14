module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadResult.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedExchangeGuardsPrimrecProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadClass
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalRawSyntaxTransport
def branchClass : Nat → Program 1
  | 4 => constant 1 1
  | 5 => succOf (succOf (.projection 0))
  | _ => constant 1 0
def atPayload (tag : Nat) : Program 1 :=
  .composition (branchClass tag) (fun _ : Fin 1 => InternalUnpair.right)
/-- Same original headClassNumber: builtins 0, application 1, ranked 2+index. -/
def headClass : Program 1 :=
  OriginalHeadEncodingBridge.choose 4 (atPayload 4)
    (OriginalHeadEncodingBridge.choose 5 (atPayload 5) (constant 1 0))
def leftClass : Program 2 := .composition headClass (fun _ : Fin 1 => .projection 0)
def rightClass : Program 2 := .composition headClass (fun _ : Fin 1 => .projection 1)
def equivalent : Program 2 := .composition InternalEqualityTest.equalityTest ![leftClass,rightClass]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadClass
