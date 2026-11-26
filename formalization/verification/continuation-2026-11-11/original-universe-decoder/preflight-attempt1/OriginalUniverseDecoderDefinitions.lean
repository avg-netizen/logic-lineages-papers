module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderValuesDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformContextMembershipDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoder
open InternalApplicationCertificateConstructors
open OriginalRawSyntaxTransport (constant succOf)
open OriginalTypedDecoder (ifSame headOf termRequestOf argumentsRequestOf liveOf)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Request selectors take [literal request, ORIGINAL outer Context]. -/
def request : Program 2 := .projection 0
def context : Program 2 := .projection 1
def mode : Program 2 := leftOf request
def typ : Program 2 := leftOf (rightOf (rightOf request))
def raw : Program 2 := rightOf (rightOf (rightOf request))
def tag : Program 2 := leftOf raw
def payload : Program 2 := rightOf raw
def domain : Program 2 := leftOf payload
def numberedHead : Program 2 := leftOf (rightOf payload)
def memberAt (M : Program 2) (type : Program 2) : Program 2 := .composition M ![type,context]
def windowAt (W : Program 2) (head : Program 2) : Program 2 := .composition W ![head,context]
def oneIf (test : Program 2) : Program 2 := ifSame test (constant 2 1) (constant 2 1) (constant 2 0)

def extraGuard (M W : Program 2) : Program 2 :=
  ifSame tag (constant 2 1) (oneIf (memberAt M domain))
    (ifSame tag (constant 2 4) (oneIf (windowAt W domain))
      (ifSame tag (constant 2 5) (oneIf (windowAt W numberedHead)) (constant 2 1)))

def guard (M W : Program 2) : Program 2 :=
  ifSame mode (constant 2 0)
    (ifSame (memberAt M typ) (constant 2 1) (extraGuard M W) (constant 2 0))
    (ifSame mode (constant 2 1) (constant 2 1) (constant 2 0))

/-- Inputs [state,outerContext]. The typed transition AST itself is retained. -/
def transition (H : Program 1) (M W : Program 2) : Program 2 :=
  ifSame (leftOf (.projection 0)) (constant 2 1)
    (InternalAcceptance.branch (rightOf (.projection 0)) (.projection 0)
      (ifSame (.composition (guard M W) ![headOf (rightOf (.projection 0)),.projection 1])
        (constant 2 1) (.composition (OriginalTypedDecoder.transition H) ![.projection 0])
        (constant 2 0))) (constant 2 0)

/-- Inputs [count,initial,outerContext]. The original outer Context is an
invariant recursion parameter, not part of the changing worklist or Gamma. -/
def iterate (H : Program 1) (M W : Program 2) : Program 3 :=
  .recursion (.projection (0 : Fin 2))
    (.composition (transition H M W) ![.projection (1 : Fin 4),.projection (3 : Fin 4)])

/-- Inputs [type/types,raw,Gamma,outerContext], using the SAME raw+1 fuel,
original request codec, state codec and children-before-suffix order. -/
def fuel : Program 4 := succOf (.projection 1)
def termInitial : Program 4 :=
  liveOf (consOf (termRequestOf (.projection 2) (.projection 0) (.projection 1)) (constant 4 0))
def argumentsInitial : Program 4 :=
  liveOf (consOf (argumentsRequestOf (.projection 2) (.projection 0) (.projection 1)) (constant 4 0))
def termRun (H : Program 1) (M W : Program 2) : Program 4 :=
  .composition (iterate H M W) ![fuel,termInitial,.projection 3]
def argumentsRun (H : Program 1) (M W : Program 2) : Program 4 :=
  .composition (iterate H M W) ![fuel,argumentsInitial,.projection 3]
def termCheck (H : Program 1) (M W : Program 2) : Program 4 :=
  .composition OriginalTypedDecoder.finished ![termRun H M W]
def argumentsCheck (H : Program 1) (M W : Program 2) : Program 4 :=
  .composition OriginalTypedDecoder.finished ![argumentsRun H M W]

/-- Inputs [packed value,pair(original Context,Encodable Gamma)]. G checks
that SAME original Context. No Gamma-in-window or erased-type test is added. -/
def source (H G : Program 1) (M W : Program 2) : Program 2 :=
  InternalAcceptance.conjunction
    (.composition G ![leftOf (.projection 1)])
    (.composition (termCheck H M W)
      ![leftOf (.projection 0),rightOf (.projection 0),rightOf (.projection 1),leftOf (.projection 1)])

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoder
