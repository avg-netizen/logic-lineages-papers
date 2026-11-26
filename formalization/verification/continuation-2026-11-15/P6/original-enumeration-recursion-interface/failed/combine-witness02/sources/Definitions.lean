module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationConstructorLayer.StatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCodeEnumerationPrimrecProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursionInterface
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructors (leftOf rightOf pairOf)
/-- Original recursion nodes are pairs(variableBound,fuel). Parameter is ignored
by rank and dependencies, exactly as the original nat_omega_rec interface. -/
def R : Program 2 := rightOf (.projection 0)
def bound : Program 2 := leftOf (.projection 0)
def previousFuel : Program 2 := .composition InternalEqualityTest.predecessor (fun _ : Fin 1 => R)
def priorNode : Program 2 := pairOf bound previousFuel
def openedNode : Program 2 := pairOf (.composition .succ (fun _ : Fin 1 => bound)) previousFuel
def positiveDependencies : Program 2 := .composition InternalListCodec.consCode
  ![priorNode,.composition InternalListCodec.consCode ![openedNode,InternalAcceptance.constantZero 2]]
def D : Program 2 := InternalAcceptance.branch R (InternalAcceptance.constantZero 2) positiveDependencies
/-- Original parameter codec is (types,(heads,(labels,tupleBound))). -/
def types : Program 3 := leftOf (.projection 2)
def heads : Program 3 := leftOf (rightOf (.projection 2))
def labels : Program 3 := leftOf (rightOf (rightOf (.projection 2)))
def tupleBound : Program 3 := rightOf (rightOf (rightOf (.projection 2)))
def variableBound : Program 3 := leftOf (.projection 0)
def fuel : Program 3 := rightOf (.projection 0)
/-- Original List.getD slots0/1 with [] default, whose code is zero.
No missing/zero-payload filtering or swapping of prior/opened. -/
def answer (i : Nat) : Program 3 := .composition InternalRawListRecursion.lookup
  ![OriginalRawSyntaxTransport.constant 3 i,.projection 1]
def positiveLayer (n : Nat) : Program 3 := .composition (OriginalEnumerationConstructorLayer.layer n)
  ![types,heads,labels,tupleBound,variableBound,answer 0,answer 1]
/-- Some[] is numeric1, not failure0. The positive branch preserves exactly
Some(original constructor layer), including malformed raw intermediate lists. -/
def G (n : Nat) : Program 3 := .composition .succ
  (fun _ : Fin 1 => InternalAcceptance.branch fuel (InternalAcceptance.constantZero 3) (positiveLayer n))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursionInterface
