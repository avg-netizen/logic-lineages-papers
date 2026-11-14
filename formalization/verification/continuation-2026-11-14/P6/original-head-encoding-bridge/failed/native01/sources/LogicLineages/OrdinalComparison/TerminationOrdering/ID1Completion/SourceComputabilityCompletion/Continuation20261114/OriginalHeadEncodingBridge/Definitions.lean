module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentMetadataFields.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadEncodingBridge
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalRawSyntaxTransport
/-- Generic Encodable sum constructors, implemented in actual arithmetic. -/
def sumLeft (p : Program 1) : Program 1 := addOf p p
def sumRight (p : Program 1) : Program 1 := succOf (sumLeft p)
def branchCode : Nat → Program 1
  | 0 => constant 1 0
  | 1 => constant 1 2
  | 2 => sumRight (sumLeft (.projection 0))
  | 3 => sumRight (sumRight (sumLeft (.projection 0)))
  | 4 => sumRight (sumRight (sumRight (sumLeft (.projection 0))))
  | 5 => sumRight (sumRight (sumRight (sumRight (.projection 0))))
  | _ => constant 1 0
def choose (tag : Nat) (yes no : Program 1) : Program 1 :=
  InternalAcceptance.branch (sameOf InternalUnpair.left (constant 1 tag)) no yes
def atPayload (tag : Nat) : Program 1 := .composition (branchCode tag) (fun _ : Fin 1 => InternalUnpair.right)
/-- Only valid headNumber inputs are asserted to encode semantic heads.
Raw unsupported tags map to zero; malformed supported payloads are not decoded. -/
def encodeHead : Program 1 :=
  choose 0 (atPayload 0) (choose 1 (atPayload 1) (choose 2 (atPayload 2)
    (choose 3 (atPayload 3) (choose 4 (atPayload 4) (choose 5 (atPayload 5) (constant 1 0))))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadEncodingBridge
