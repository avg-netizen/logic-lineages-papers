module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStructuralEndpointGuardDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStack
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Literal original application code, with the two TERM PAYLOADS as inputs. -/
def applicationValue (d e fp ap : Nat) : Nat :=
  Nat.pair e (Nat.pair 2 (Nat.pair d (Nat.pair fp ap)))

def functionValue (d e fp : Nat) : Nat := Nat.pair (1 + Nat.pair d e) fp
def argumentValue (d ap : Nat) : Nat := Nat.pair d ap

/-- Selectors are total on every raw packed number, not only decoded terms. -/
def resultTypeValue (value : Nat) : Nat := (Nat.unpair value).1
def payloadValue (value : Nat) : Nat := (Nat.unpair value).2
def tagValue (value : Nat) : Nat := (Nat.unpair (payloadValue value)).1
def bodyValue (value : Nat) : Nat := (Nat.unpair (payloadValue value)).2
def domainValue (value : Nat) : Nat := (Nat.unpair (bodyValue value)).1
def functionPayloadValue (value : Nat) : Nat :=
  (Nat.unpair (Nat.unpair (bodyValue value)).2).1
def argumentPayloadValue (value : Nat) : Nat :=
  (Nat.unpair (Nat.unpair (bodyValue value)).2).2
def functionChildValue (value : Nat) : Nat :=
  functionValue (domainValue value) (resultTypeValue value) (functionPayloadValue value)
def argumentChildValue (value : Nat) : Nat :=
  argumentValue (domainValue value) (argumentPayloadValue value)

/-- Status one means live or successfully finished. Every other status is
rejected. The stack uses the unchanged original successor/pair list codec. -/
structure State where
  status : Nat
  work : List Nat

def encodeState (state : State) : Nat :=
  Nat.pair state.status (NumberedMultisetNumeric.numbersNumber state.work)

def failedState : State := ⟨0, []⟩

/-- Only an application node is opened. Every non-application node delegates
its WHOLE original packed value to the supplied leaf. Both tests accept exactly
at one. The first child is the typed function, followed by the typed argument. -/
def stateStep (node leaf : Nat → Nat) (state : State) : State :=
  if state.status = 1 then
    match state.work with
    | [] => state
    | value :: rest =>
      if tagValue value = 2 then
        if node (resultTypeValue value) = 1 then
          ⟨1, functionChildValue value :: argumentChildValue value :: rest⟩
        else failedState
      else if leaf value = 1 then ⟨1, rest⟩ else failedState
  else failedState

/-- The direct numeric transition on ALL raw states. No decoder success,
well-formed state, window closure, or term-validity premise is used. -/
def transitionValue (node leaf : Nat → Nat) (state : Nat) : Nat :=
  if (Nat.unpair state).1 = 1 then
    let work := (Nat.unpair state).2
    if work = 0 then state else
      let value := (Nat.unpair (work - 1)).1
      let rest := (Nat.unpair (work - 1)).2
      if tagValue value = 2 then
        if node (resultTypeValue value) = 1 then
          Nat.pair 1 (1 + Nat.pair (functionChildValue value)
            (1 + Nat.pair (argumentChildValue value) rest))
        else 0
      else if leaf value = 1 then Nat.pair 1 rest else 0
  else 0

/-- This is an external invariant about ORIGINAL validity, not an internal
derivability premise. In particular it is not a field of Program data. -/
def stateValid (valid : Nat → Nat) (state : State) : Prop :=
  state.status = 1 ∧ ∀ value ∈ state.work, valid value = 1

/-- Reconstructed arrow type codes can grow. The termination measure ignores
them and sums the original TERM PAYLOAD plus one for every pending node. -/
def workWeight (work : List Nat) : Nat :=
  (work.map (fun value => payloadValue value + 1)).sum

def status : Program 1 := InternalUnpair.left
def work : Program 1 := InternalUnpair.right
def current : Program 1 :=
  .composition InternalListCodec.headCode (fun _ : Fin 1 => work)
def rest : Program 1 :=
  .composition InternalListCodec.tailCode (fun _ : Fin 1 => work)
def currentType : Program 1 := leftOf current
def currentTag : Program 1 := InternalApplicationStepPeel.constructorTag current
def currentDomain : Program 1 := InternalApplicationStepPeel.appDomain current
def currentFunction : Program 1 :=
  pairOf (consOf currentDomain currentType)
    (InternalApplicationStepPeel.functionPayload current)
def currentArgument : Program 1 :=
  pairOf currentDomain (InternalApplicationStepPeel.argumentPayload current)

def exactOne {n : Nat} (p : Program n) : Program n :=
  InternalApplicationStepPeel.same p (InternalLessThan.constantOne n)

def popped : Program 1 := pairOf (InternalLessThan.constantOne 1) rest
def expanded : Program 1 := pairOf (InternalLessThan.constantOne 1)
  (consOf currentFunction (consOf currentArgument rest))

/-- A concrete original unary PR AST. No representability witness is chosen.
The node guard receives the result type; the leaf receives the packed value. -/
def transition (node leaf : Program 1) : Program 1 :=
  InternalAcceptance.branch (exactOne status) (InternalAcceptance.constantZero 1)
    (InternalAcceptance.branch work (.projection 0)
      (InternalAcceptance.branch
        (InternalApplicationStepPeel.same currentTag (two 1))
        (InternalAcceptance.branch
          (exactOne (.composition leaf (fun _ : Fin 1 => current)))
          (InternalAcceptance.constantZero 1) popped)
        (InternalAcceptance.branch
          (exactOne (.composition node (fun _ : Fin 1 => currentType)))
          (InternalAcceptance.constantZero 1) expanded)))

/-- Inputs [count,initial]. The recursion index is deliberately ignored. -/
def iterate (node leaf : Program 1) : Program 2 :=
  .recursion (.projection (0 : Fin 1))
    (.composition (transition node leaf) (fun _ : Fin 1 => .projection (1 : Fin 3)))

def fuel : Program 1 := .composition .succ (fun _ : Fin 1 => InternalUnpair.right)
def initial : Program 1 := pairOf (InternalLessThan.constantOne 1)
  (consOf (.projection 0) (InternalAcceptance.constantZero 1))
def run (node leaf : Program 1) : Program 1 :=
  .composition (iterate node leaf) ![fuel,initial]
def finished : Program 1 := InternalAcceptance.conjunction (exactOne status)
  (InternalApplicationStepPeel.same work (InternalAcceptance.constantZero 1))

/-- The complete bounded AST is exposed now, but its all-input calibration and
internal recursive application law are NOT targets paid by the one-step packet. -/
def validator (node leaf : Program 1) : Program 1 :=
  .composition finished (fun _ : Fin 1 => run node leaf)

/-- Target validity has NO universe filter. Universe recursion applies the
original result-type membership guard only at application nodes, and otherwise
retains the original source-universe leaf. Source implies target syntactically. -/
def recursiveData (old : InternalOriginalStepGuard.Data) (member : Program 1) :
    InternalOriginalStepGuard.Data :=
  let target := validator (InternalLessThan.constantOne 1) old.targetValid
  let universeValidator := validator member old.sourceValid
  ⟨InternalAcceptance.conjunction target universeValidator, target⟩

/-- Inputs [domain,codomain,functionPayload,argumentPayload,stackTail]. These
are exact original constructor ASTs, not a new encoding of source terms. -/
def applicationFrame : Program 5 :=
  pairOf (InternalLessThan.constantOne 5)
    (consOf (.composition packedApplication ![.projection 0,.projection 1,
      .projection 2,.projection 3]) (.projection 4))

def expandedFrame : Program 5 :=
  pairOf (InternalLessThan.constantOne 5)
    (consOf (pairOf (consOf (.projection 0) (.projection 1)) (.projection 2))
      (consOf (pairOf (.projection 0) (.projection 3)) (.projection 4)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStack
