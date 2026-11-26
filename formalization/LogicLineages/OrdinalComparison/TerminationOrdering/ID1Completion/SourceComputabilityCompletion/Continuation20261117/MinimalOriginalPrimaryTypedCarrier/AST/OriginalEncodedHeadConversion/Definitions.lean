module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.NumericDependencyCross.Definitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListMapDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.MinimalOriginalPrimaryTypedCarrier.AST.OriginalEncodedHeadConversion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructors
open OriginalRawSyntaxTransport (constant succOf sameOf)
/-- State pair(quotient,remainder) for binary sum encoding; start pair(0,0)=0.
At each successor, toggle remainder, increment quotient only at remainder1. -/
def splitStep : Program 2 := InternalAcceptance.branch (rightOf (.projection 1))
  (pairOf (leftOf (.projection 1)) (constant 2 1))
  (pairOf (succOf (leftOf (.projection 1))) (constant 2 0))
def split : Program 1 := .recursion (constant 0 0) splitStep
def half : Program 1 := .composition InternalUnpair.left (fun _ : Fin 1 => split)
def bit : Program 1 := .composition InternalUnpair.right (fun _ : Fin 1 => split)
/-- Decode one actual Encodable sum constructor (even=inl, odd=inr),
passing the quotient to the chosen branch. -/
def sumCase (left right : Program 1) : Program 1 := InternalAcceptance.branch bit
  (.composition left (fun _ : Fin 1 => half))
  (.composition right (fun _ : Fin 1 => half))
/-- Bool payload0 maps rawzero0; payload1 maps rawsucc pair(1,0).
Every other Bool payload is invalid and deliberately maps default0. -/
def booleanHead : Program 1 := InternalAcceptance.branch
  (sameOf (.projection 0) (constant 1 1)) (constant 1 0)
  (pairOf (constant 1 1) (constant 1 0))
def payloadHead (tag : Nat) : Program 1 := pairOf (constant 1 tag) (.projection 0)
/-- Preserve the ORIGINAL Fin n restriction, including n=0; invalid→0. -/
def rankedHead (n : Nat) : Program 1 := InternalAcceptance.branch
  (.composition InternalLessThan.ltTest ![.projection 0,constant 1 n])
  (constant 1 0) (payloadHead 5)
/-- ORIGINAL HeadData nesting: Bool + (Ty + (Ty + (Ty×Ty + Fin n))).
Ty and Ty×Ty decoding is total with original numeric codecs; Bool/Fin failures
are defaulted to raw0, not silently turned into a successful typed head. -/
def convert (n : Nat) : Program 1 := sumCase booleanHead
  (sumCase (payloadHead 2) (sumCase (payloadHead 3)
    (sumCase (payloadHead 4) (rankedHead n))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.MinimalOriginalPrimaryTypedCarrier.AST.OriginalEncodedHeadConversion
