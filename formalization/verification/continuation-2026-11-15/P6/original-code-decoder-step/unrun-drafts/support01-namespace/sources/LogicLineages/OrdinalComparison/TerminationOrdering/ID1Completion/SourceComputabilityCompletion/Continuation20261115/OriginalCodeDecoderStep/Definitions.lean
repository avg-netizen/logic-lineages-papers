module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalHeadDecoderValidity.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesChildren.Definitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCodeParserTableTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderStep
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructors OriginalRawSyntaxTransport
/-- Inputs [previous numeric table, raw code], with the ORIGINAL raw code codec. -/
def raw : Program 2 := .projection 1
def tag : Program 2 := leftOf raw
def payload : Program 2 := rightOf raw
def firstField : Program 2 := firstOf raw
def secondField : Program 2 := secondOf raw
/-- Only tags 4/5 consume this field. All other values are observationally irrelevant. -/
def headField : Program 2 := InternalAcceptance.branch (sameOf tag (constant 2 5))
  (leftOf payload) (leftOf (rightOf payload))
/-- Exact-one interpretation; original lookup is zero past the end of a raw list. -/
def childAt (child : Program 2) : Program 2 := sameOf
  (.composition InternalRawListRecursion.lookup ![child,.projection 0]) (constant 2 1)
def firstAccepted : Program 2 := childAt firstField
def secondAccepted : Program 2 := childAt secondField
def headAccepted (n : Nat) : Program 2 :=
  .composition (OriginalHeadDecoderValidity.check n) (fun _ : Fin 1 => headField)
def bothChildren : Program 2 := InternalAcceptance.conjunction firstAccepted secondAccepted
def ordinary (n : Nat) : Program 2 := InternalAcceptance.conjunction (headAccepted n) firstAccepted
def numbered (n : Nat) : Program 2 := InternalAcceptance.conjunction
  (InternalAcceptance.conjunction (headAccepted n) firstAccepted) secondAccepted
def choose (k : Nat) (yes no : Program 2) : Program 2 :=
  InternalAcceptance.branch (sameOf tag (constant 2 k)) no yes
/-- Literal codeNext after the paid total type/type-list decoders are eliminated.
This is ONE table step, not the recursive guard or installed dependency supplier. -/
def step (n : Nat) : Program 2 :=
  choose 0 (constant 2 1) (choose 1 firstAccepted
    (choose 2 bothChildren (choose 3 (constant 2 1)
      (choose 4 (ordinary n) (choose 5 (numbered n)
        (choose 6 (sameOf payload (constant 2 0)) (choose 7 bothChildren (constant 2 0))))))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderStep
