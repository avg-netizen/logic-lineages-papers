module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.StatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.StatementChecks
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructors OriginalRawSyntaxTransport
open Continuation20261114 Continuation20261115
open TwoSol20261113.CalibratedPrimary.Membership (contains)
/-- Literal boolean conjunction. Every caller below supplies booleans. -/
def both {k : Nat} (p q : Program k) : Program k := InternalAcceptance.branch p (constant k 0) q
/-- Check actual original type-list entries against allowed types; inputs [list,allowed]. -/
def allStep : Program 3 := both (.composition contains ![.projection 2,.projection 0]) (.projection 1)
def allTypes : Program 2 := InternalRawListRecursion.listRec (constant 1 1) allStep
/-- Key is pair(rawCode,variableBound); parameter is pair(types,pair(heads,pair(labels,tupleBound))). -/
def keyRaw {k : Nat} (key : Program k) : Program k := leftOf key
def keyBound {k : Nat} (key : Program k) : Program k := rightOf key
def rank : Program 2 := keyRaw (.projection 0)
def childBound : Program 2 := InternalAcceptance.branch
  (sameOf (leftOf (keyRaw (.projection 0))) (constant 2 1))
  (keyBound (.projection 0)) (succOf (keyBound (.projection 0)))
def firstKey : Program 2 := pairOf (firstOf (keyRaw (.projection 0))) childBound
def secondKey : Program 2 := pairOf (secondOf (keyRaw (.projection 0))) (keyBound (.projection 0))
/-- Children are keyed, ordered, and lambda alone opens the bound. No depth cache is reused. -/
def dependency : Program 2 := InternalAcceptance.branch (arityOf (keyRaw (.projection 0)))
  (constant 2 0)
  (InternalAcceptance.branch (sameOf (arityOf (keyRaw (.projection 0))) (constant 2 2))
    (consOf firstKey (constant 2 0)) (consOf firstKey (consOf secondKey (constant 2 0))))
/-- Layer inputs [key,answers,param]. -/
def raw : Program 3 := keyRaw (.projection 0)
def bound : Program 3 := keyBound (.projection 0)
def tag : Program 3 := leftOf raw
def payload : Program 3 := rightOf raw
def types : Program 3 := leftOf (.projection 2)
def heads : Program 3 := leftOf (rightOf (.projection 2))
def labels : Program 3 := leftOf (rightOf (rightOf (.projection 2)))
def tupleBound : Program 3 := rightOf (rightOf (rightOf (.projection 2)))
def firstAnswer : Program 3 := .composition InternalListCodec.headCode ![.projection 1]
def secondAnswer : Program 3 := .composition InternalListCodec.headCode
  ![.composition InternalListCodec.tailCode ![.projection 1]]
def typeMember (ty : Program 3) : Program 3 := .composition contains ![types,ty]
def headMember (n : Nat) (h : Program 3) : Program 3 := .composition contains
  ![.composition (OriginalEncodedNumberedEnumerationBranch.convertedHeads n) ![heads],h]
def variableBranch : Program 3 := .composition InternalLessThan.ltTest ![payload,bound]
def lambdaBranch : Program 3 := both (typeMember (leftOf payload)) firstAnswer
def binaryBranch : Program 3 := both (typeMember (leftOf payload)) (both firstAnswer secondAnswer)
def bottomBranch : Program 3 := typeMember payload
def ordinaryBranch (n : Nat) : Program 3 := both (headMember n (leftOf payload)) firstAnswer
def numberedLabel : Program 3 := leftOf payload
def numberedHead : Program 3 := leftOf (rightOf payload)
def numberedType : Program 3 := leftOf (rightOf (rightOf payload))
def numberedTypes : Program 3 := leftOf (rightOf (rightOf (rightOf (rightOf payload))))
def numberedBranch (n : Nat) : Program 3 :=
  both (.composition InternalLessThan.ltTest ![numberedLabel,succOf labels])
    (both (headMember n numberedHead)
      (both (typeMember numberedType)
        (both firstAnswer
          (both (.composition InternalLessThan.ltTest
            ![.composition OriginalContextInsertion.length ![numberedTypes],succOf tupleBound])
            (both (.composition allTypes ![numberedTypes,types]) secondAnswer)))))
/-- Original eight tags; unknown tags reject. The independent decoder guard also
rejects malformed metadata, head bounds and nil payloads. -/
def choose (n : Nat) : Program 3 :=
  InternalAcceptance.branch (sameOf tag (constant 3 0))
    (InternalAcceptance.branch (sameOf tag (constant 3 1))
      (InternalAcceptance.branch (sameOf tag (constant 3 2))
        (InternalAcceptance.branch (sameOf tag (constant 3 3))
          (InternalAcceptance.branch (sameOf tag (constant 3 4))
            (InternalAcceptance.branch (sameOf tag (constant 3 5))
              (InternalAcceptance.branch (sameOf tag (constant 3 6))
                (InternalAcceptance.branch (sameOf tag (constant 3 7))
                  (constant 3 0) binaryBranch)
                (constant 3 1))
              (numberedBranch n))
            (ordinaryBranch n))
          bottomBranch)
        binaryBranch)
      lambdaBranch)
    variableBranch
/-- Fresh selected-recursion answer: Some(boolean), encoded by one successor.
No caller supplies successful recursive values or original Fields truth. -/
def layer (n : Nat) : Program 3 := succOf
  (both (.composition (OriginalCodeValidityGuard.check n) ![raw]) (choose n))
def graph (n : Nat) : Program 3 := ExchangeGraphRecursion.graph rank dependency (layer n)
def extract (n : Nat) : Program 2 := ExchangeSelectedRecursor.exchange rank dependency (layer n)
/-- Public arguments [raw,variableBound,types,original encoded heads,labels,tupleBound]. -/
def fields (n : Nat) : Program 6 := .composition (extract n)
  ![pairOf (.projection 0) (.projection 1),
    pairOf (.projection 2) (pairOf (.projection 3) (pairOf (.projection 4) (.projection 5)))]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields
