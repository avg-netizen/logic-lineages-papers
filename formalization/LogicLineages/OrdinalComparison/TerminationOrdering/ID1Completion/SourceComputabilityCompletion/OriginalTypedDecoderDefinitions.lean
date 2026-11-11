module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderValuesDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableDecoderDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoder
open InternalApplicationCertificateConstructors
open OriginalRawSyntaxTransport (constant succOf sameOf)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

def programValue (H : Program 1) (value : Nat) : Nat :=
  evaluate H (List.Vector.ofFn ![value])

/-- The branch convention is control, zero branch, nonzero branch. -/
def ifSame {n : Nat} (x y yes no : Program n) : Program n :=
  InternalAcceptance.branch (sameOf x y) no yes

def predecessorOf {n : Nat} (p : Program n) : Program n :=
  .composition InternalEqualityTest.predecessor (fun _ : Fin 1 => p)
def headOf {n : Nat} (p : Program n) : Program n := leftOf (predecessorOf p)
def tailOf {n : Nat} (p : Program n) : Program n := rightOf (predecessorOf p)
def liveOf {n : Nat} (work : Program n) : Program n := pairOf (constant n 1) work

def termRequestOf {n : Nat} (gamma typ raw : Program n) : Program n :=
  pairOf (constant n 0) (pairOf gamma (pairOf typ raw))
def argumentsRequestOf {n : Nat} (gamma types raw : Program n) : Program n :=
  pairOf (constant n 1) (pairOf gamma (pairOf types raw))

/-- All selectors act on the ACTUAL connected state/request/raw code. -/
def status : Program 1 := InternalUnpair.left
def work : Program 1 := InternalUnpair.right
def currentRequest : Program 1 := headOf work
def rest : Program 1 := tailOf work
def mode : Program 1 := leftOf currentRequest
def gamma : Program 1 := leftOf (rightOf currentRequest)
def typ : Program 1 := leftOf (rightOf (rightOf currentRequest))
def raw : Program 1 := rightOf (rightOf (rightOf currentRequest))
def tag : Program 1 := leftOf raw
def payload : Program 1 := rightOf raw
def domain : Program 1 := leftOf payload
def unaryChild : Program 1 := rightOf payload
def firstChild : Program 1 := leftOf (rightOf payload)
def secondChild : Program 1 := rightOf (rightOf payload)
def expectedDomain : Program 1 := headOf typ
def expectedTail : Program 1 := tailOf typ
def numberedHead : Program 1 := leftOf (rightOf payload)
def numberedType : Program 1 := leftOf (rightOf (rightOf payload))
def numberedBase : Program 1 := leftOf (rightOf (rightOf (rightOf payload)))
def numberedTypes : Program 1 := leftOf (rightOf (rightOf (rightOf (rightOf payload))))
def numberedExtras : Program 1 := rightOf (rightOf (rightOf (rightOf (rightOf payload))))

def variableCheck : Program 1 := .composition OriginalVariableDecoder.check ![typ,payload,gamma]
def ordinarySignature (H : Program 1) : Program 1 := .composition H (fun _ : Fin 1 => domain)
def numberedSignature (H : Program 1) : Program 1 := .composition H (fun _ : Fin 1 => numberedHead)

def pop : Program 1 := liveOf rest
def pushOne (child : Program 1) : Program 1 := liveOf (consOf child rest)
def pushTwo (first second : Program 1) : Program 1 := liveOf (consOf first (consOf second rest))

def variableStep : Program 1 := ifSame variableCheck (constant 1 1) pop (constant 1 0)
def lambdaStep : Program 1 :=
  InternalAcceptance.branch typ (constant 1 0)
    (ifSame expectedDomain domain
      (pushOne (termRequestOf (consOf domain gamma) expectedTail unaryChild)) (constant 1 0))
def applicationStep : Program 1 :=
  pushTwo (termRequestOf gamma (consOf domain typ) firstChild)
    (termRequestOf gamma domain secondChild)
def bottomStep : Program 1 := ifSame payload typ pop (constant 1 0)
def ordinaryStep (H : Program 1) : Program 1 :=
  InternalAcceptance.branch (ordinarySignature H) (constant 1 0)
    (ifSame (headOf (ordinarySignature H)) typ
      (pushOne (argumentsRequestOf gamma (tailOf (ordinarySignature H)) unaryChild)) (constant 1 0))
def numberedStep (H : Program 1) : Program 1 :=
  InternalAcceptance.branch (numberedSignature H) (constant 1 0)
    (ifSame numberedType typ
      (pushTwo (argumentsRequestOf gamma (tailOf (numberedSignature H)) numberedBase)
        (argumentsRequestOf gamma numberedTypes numberedExtras)) (constant 1 0))
def nilStep : Program 1 :=
  ifSame payload (constant 1 0) (ifSame typ (constant 1 0) pop (constant 1 0)) (constant 1 0)
def consStep : Program 1 :=
  InternalAcceptance.branch typ (constant 1 0)
    (ifSame expectedDomain domain
      (pushTwo (termRequestOf gamma domain firstChild)
        (argumentsRequestOf gamma expectedTail secondChild)) (constant 1 0))

def termDispatch (H : Program 1) : Program 1 :=
  ifSame tag (constant 1 0) variableStep
    (ifSame tag (constant 1 1) lambdaStep
      (ifSame tag (constant 1 2) applicationStep
        (ifSame tag (constant 1 3) bottomStep
          (ifSame tag (constant 1 4) (ordinaryStep H)
            (ifSame tag (constant 1 5) (numberedStep H) (constant 1 0))))))
def argumentsDispatch : Program 1 :=
  ifSame tag (constant 1 6) nilStep (ifSame tag (constant 1 7) consStep (constant 1 0))

def transition (H : Program 1) : Program 1 :=
  ifSame status (constant 1 1)
    (InternalAcceptance.branch work (.projection 0)
      (ifSame mode (constant 1 0) (termDispatch H)
        (ifSame mode (constant 1 1) argumentsDispatch (constant 1 0)))) (constant 1 0)

/-- Inputs [count,initial]. The recursive accumulator is the entire state. -/
def iterate (H : Program 1) : Program 2 :=
  .recursion (.projection (0 : Fin 1))
    (.composition (transition H) (fun _ : Fin 1 => .projection (1 : Fin 3)))

def finished : Program 1 :=
  ifSame status (constant 1 1)
    (ifSame work (constant 1 0) (constant 1 1) (constant 1 0)) (constant 1 0)

/-- Inputs [requested type/types, original raw codeNumber, Encodable Gamma]. -/
def fuel : Program 3 := succOf (.projection 1)
def termInitial : Program 3 :=
  liveOf (consOf (termRequestOf (.projection 2) (.projection 0) (.projection 1)) (constant 3 0))
def argumentsInitial : Program 3 :=
  liveOf (consOf (argumentsRequestOf (.projection 2) (.projection 0) (.projection 1)) (constant 3 0))
def termRun (H : Program 1) : Program 3 := .composition (iterate H) ![fuel,termInitial]
def argumentsRun (H : Program 1) : Program 3 := .composition (iterate H) ![fuel,argumentsInitial]
def termCheck (H : Program 1) : Program 3 := .composition finished (fun _ : Fin 1 => termRun H)
def argumentsCheck (H : Program 1) : Program 3 := .composition finished (fun _ : Fin 1 => argumentsRun H)

/-- Inputs [original packedNumber, Encodable Gamma]. -/
def packedCheck (H : Program 1) : Program 2 :=
  .composition (termCheck H) ![leftOf (.projection 0),rightOf (.projection 0),.projection 1]

/-- The mandatory ORIGINAL context guard is outside the transparent traversal.
Inputs [packed value, pair(original context, Encodable Gamma)] are unchanged. -/
def target (H G : Program 1) : Program 2 :=
  InternalAcceptance.conjunction
    (.composition G (fun _ : Fin 1 => leftOf (.projection 1)))
    (.composition (termCheck H) ![leftOf (.projection 0),rightOf (.projection 0),rightOf (.projection 1)])

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoder
