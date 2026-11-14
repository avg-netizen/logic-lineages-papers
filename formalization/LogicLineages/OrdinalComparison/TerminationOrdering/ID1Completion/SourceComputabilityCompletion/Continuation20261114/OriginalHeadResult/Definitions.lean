module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadEncodingBridge.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadResult
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalRawSyntaxTransport
/-- The literal numeric type constructor, not generic head encoding. -/
def arrow (p q : Program 1) : Program 1 :=
  succOf (.composition InternalPairing.pairing ![p,q])
def branchResult : Nat → Program 1
  | 0 => constant 1 0
  | 1 => arrow (constant 1 0) (constant 1 0)
  | 2 => arrow (constant 1 0) (arrow (.projection 0) (arrow (.projection 0) (.projection 0)))
  | 3 => arrow (constant 1 0)
      (arrow (arrow (constant 1 0) (arrow (.projection 0) (.projection 0)))
        (arrow (.projection 0) (.projection 0)))
  | 4 => InternalUnpair.right
  | _ => constant 1 0
def atPayload (tag : Nat) : Program 1 :=
  .composition (branchResult tag) (fun _ : Fin 1 => InternalUnpair.right)
/-- Valid raw head codes are calibrated below. Unsupported tags return zero;
no semantic meaning is assigned to malformed type payloads here. -/
def headResult : Program 1 :=
  OriginalHeadEncodingBridge.choose 0 (atPayload 0)
    (OriginalHeadEncodingBridge.choose 1 (atPayload 1)
      (OriginalHeadEncodingBridge.choose 2 (atPayload 2)
        (OriginalHeadEncodingBridge.choose 3 (atPayload 3)
          (OriginalHeadEncodingBridge.choose 4 (atPayload 4)
            (OriginalHeadEncodingBridge.choose 5 (atPayload 5) (constant 1 0))))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadResult
