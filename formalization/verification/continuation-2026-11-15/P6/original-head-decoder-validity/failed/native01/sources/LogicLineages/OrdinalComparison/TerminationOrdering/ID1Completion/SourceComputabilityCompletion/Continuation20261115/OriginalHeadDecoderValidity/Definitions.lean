module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadEncodingBridge.Definitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedHeadCodecPrimrecTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalHeadDecoderValidity
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalRawSyntaxTransport
/-- The original head codec accepts basic tags only with payload zero. -/
def basicPayload : Program 1 := sameOf InternalUnpair.right (constant 1 0)
/-- Ranked head syntax depends on the finite symbol bound, not its arity or a window. -/
def rankedPayload (n : Nat) : Program 1 :=
  .composition InternalLessThan.ltTest ![InternalUnpair.right,constant 1 n]
/-- Exact syntactic head-decoder guard, NOT HeadInWindow or typed acceptance.
Type/type-pair numeric decoding is total, hence tags 2/3/4 accept every payload. -/
def check (n : Nat) : Program 1 :=
  Continuation20261114.OriginalHeadEncodingBridge.choose 0 basicPayload
    (Continuation20261114.OriginalHeadEncodingBridge.choose 1 basicPayload
      (Continuation20261114.OriginalHeadEncodingBridge.choose 2 (constant 1 1)
        (Continuation20261114.OriginalHeadEncodingBridge.choose 3 (constant 1 1)
          (Continuation20261114.OriginalHeadEncodingBridge.choose 4 (constant 1 1)
            (Continuation20261114.OriginalHeadEncodingBridge.choose 5 (rankedPayload n) (constant 1 0))))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalHeadDecoderValidity
