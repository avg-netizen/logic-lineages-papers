module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListMapDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservations
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructors
open OriginalRawSyntaxTransport (constant succOf)
/-- Walker state is pair(remaining raw tag6/tag7 spine, reversed numeric list).
The runtime parameter remains external and unchanged. Unknown raw tags stop
and retain the prefix already collected; there is no implicit validity test. -/
def remaining : Program 2 := leftOf (.projection 0)
def accumulated : Program 2 := rightOf (.projection 0)
def payload : Program 2 := rightOf remaining
def childType : Program 2 := leftOf payload
def childRaw : Program 2 := leftOf (rightOf payload)
def tailRaw : Program 2 := rightOf (rightOf payload)
def childPacked : Program 2 := pairOf childType childRaw
def childObservation (R : Program 2) : Program 2 := .composition R ![childPacked,.projection 1]
def typedObservation (R : Program 2) : Program 2 := pairOf childType (childObservation R)
def advance (R : Program 2) : Program 2 := pairOf tailRaw (consOf (typedObservation R) accumulated)
def walkStep (R : Program 2) : Program 2 :=
 OriginalTypedDecoder.ifSame (leftOf remaining) (constant 2 7) (advance R) (.projection 0)
/-- Inputs [fuel,initial state,parameter]; original primitive recursion. -/
def walk (R : Program 2) : Program 3 := .recursion (.projection 0)
 (.composition (walkStep R) ![.projection 1,.projection 3])
def initial : Program 2 := pairOf (.projection 0) (constant 2 0)
def walked (R : Program 2) : Program 2 :=
 .composition (walk R) ![succOf (.projection 0),initial,.projection 1]
def reversedObservations (R : Program 2) : Program 2 := rightOf (walked R)

/-- Separate numeric reversal; zero stops, a positive list uses its literal
predecessor-pair head/tail. This is NOT applied directly to tag7 syntax. -/
def reverseRemaining : Program 1 := InternalUnpair.left
def reverseAccumulated : Program 1 := InternalUnpair.right
def reverseAdvance : Program 1 := pairOf
 (.composition InternalListCodec.tailCode (fun _ : Fin 1 => reverseRemaining))
 (consOf (.composition InternalListCodec.headCode (fun _ : Fin 1 => reverseRemaining)) reverseAccumulated)
def reverseStep : Program 1 := InternalAcceptance.branch reverseRemaining (.projection 0) reverseAdvance
/-- Inputs [fuel,state]. -/
def reverseRun : Program 2 := .recursion (.projection 0)
 (.composition reverseStep (fun _ : Fin 1 => .projection 1))
def reverse : Program 1 := rightOf (.composition reverseRun
 ![succOf (.projection 0),pairOf (.projection 0) (constant 1 0)])
/-- Inputs [raw typed-argument spine, original parameter]. BASE sorting is
external; this converter retains the original order, including duplicates. -/
def argumentObservations (R : Program 2) : Program 2 :=
 .composition reverse (fun _ : Fin 1 => reversedObservations R)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservations
