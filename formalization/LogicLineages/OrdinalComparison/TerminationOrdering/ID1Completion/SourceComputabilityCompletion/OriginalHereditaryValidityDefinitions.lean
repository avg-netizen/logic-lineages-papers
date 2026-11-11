module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPairingSumBoundsDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomParameterDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidity
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalOriginalUniformDescentSelection (Data)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- A pending ORIGINAL raw packed value and its own original runtime parameter.
The parameter is pair(context, encoded Gamma), not typesNumber Gamma. -/
structure Frame where
  raw : Nat
  parameter : Nat

def encodeFrame (frame : Frame) : Nat := Nat.pair frame.raw frame.parameter

/-- Status one is live or successfully finished. The worklist uses the
unchanged successor/pair list codec, now with literal pair-coded frames. -/
structure State where
  status : Nat
  work : List Frame

def encodeState (state : State) : Nat :=
  Nat.pair state.status
    (NumberedMultisetNumeric.numbersNumber (state.work.map encodeFrame))

def failedState : State := ⟨0, []⟩

abbrev resultTypeValue := InternalApplicationValidityStack.resultTypeValue
abbrev payloadValue := InternalApplicationValidityStack.payloadValue
abbrev tagValue := InternalApplicationValidityStack.tagValue
abbrev domainValue := InternalApplicationValidityStack.domainValue
abbrev functionPayloadValue := InternalApplicationValidityStack.functionPayloadValue
abbrev argumentPayloadValue := InternalApplicationValidityStack.argumentPayloadValue
abbrev functionChildValue := InternalApplicationValidityStack.functionChildValue
abbrev argumentChildValue := InternalApplicationValidityStack.argumentChildValue

/-- Total original selectors. The lambda codomain comes from the outer
successor/pair arrow number, while its domain comes from the actual payload. -/
def lambdaCodomainValue (value : Nat) : Nat :=
  (Nat.unpair (resultTypeValue value - 1)).2

def lambdaBodyPayloadValue (value : Nat) : Nat :=
  (Nat.unpair (Nat.unpair (payloadValue value)).2).2

def lambdaBodyValue (value : Nat) : Nat :=
  Nat.pair (lambdaCodomainValue value) (lambdaBodyPayloadValue value)

/-- Only encoded Gamma is extended. The original outer context is retained,
and the domain is the ACTUAL original lambda payload field. -/
def childParameterValue (value parameter : Nat) : Nat :=
  Nat.pair (Nat.unpair parameter).1
    (1 + Nat.pair (domainValue value) (Nat.unpair parameter).2)

/-- Every visited node checks both original leaves at its OWN parameter.
Only literal tag two adds the original outer-type membership test. All
outputs other than exactly one reject, even for arbitrary non-Boolean leaves. -/
def nodeCheckValue (oldSource oldTarget member : Nat → Nat → Nat)
    (value parameter : Nat) : Nat :=
  if oldSource value parameter = 1 then
    if oldTarget value parameter = 1 then
      if tagValue value = 2 then
        if member (resultTypeValue value) parameter = 1 then 1 else 0
      else 1
    else 0
  else 0

/-- Applications push the actual typed function and argument at the SAME
parameter. Lambdas push the actual typed body at the single extended Gamma.
Other tags pop. There is no semantic validity test or proof field here. -/
def stateStep (oldSource oldTarget member : Nat → Nat → Nat) (state : State) : State :=
  if state.status = 1 then
    match state.work with
    | [] => state
    | frame :: rest =>
      if nodeCheckValue oldSource oldTarget member frame.raw frame.parameter = 1 then
        if tagValue frame.raw = 2 then
          ⟨1, ⟨functionChildValue frame.raw, frame.parameter⟩ ::
            ⟨argumentChildValue frame.raw, frame.parameter⟩ :: rest⟩
        else if tagValue frame.raw = 1 then
          ⟨1, ⟨lambdaBodyValue frame.raw,
            childParameterValue frame.raw frame.parameter⟩ :: rest⟩
        else ⟨1, rest⟩
      else failedState
  else failedState

/-- Direct numeric transition on EVERY raw state, including malformed frames,
parameters, values and non-one statuses. There is no decoder premise. -/
def transitionValue (oldSource oldTarget member : Nat → Nat → Nat) (state : Nat) : Nat :=
  if (Nat.unpair state).1 = 1 then
    let work := (Nat.unpair state).2
    if work = 0 then state else
      let frame := (Nat.unpair (work - 1)).1
      let rest := (Nat.unpair (work - 1)).2
      let value := (Nat.unpair frame).1
      let parameter := (Nat.unpair frame).2
      if nodeCheckValue oldSource oldTarget member value parameter = 1 then
        if tagValue value = 2 then
          Nat.pair 1 (1 + Nat.pair (Nat.pair (functionChildValue value) parameter)
            (1 + Nat.pair (Nat.pair (argumentChildValue value) parameter) rest))
        else if tagValue value = 1 then
          Nat.pair 1 (1 + Nat.pair
            (Nat.pair (lambdaBodyValue value) (childParameterValue value parameter)) rest)
        else Nat.pair 1 rest
      else 0
  else 0

/-- Neither reconstructed type codes, runtime parameters nor frame codes
contribute to fuel. Every pending ORIGINAL term payload contributes plus one. -/
def workWeight (work : List Frame) : Nat :=
  (work.map (fun frame => payloadValue frame.raw + 1)).sum

def initialValue (value parameter : Nat) : Nat :=
  Nat.pair 1 (1 + Nat.pair (Nat.pair value parameter) 0)

def iterateValue (oldSource oldTarget member : Nat → Nat → Nat)
    (count initial : Nat) : Nat :=
  Nat.rec initial (fun _ state => transitionValue oldSource oldTarget member state) count

def runValue (oldSource oldTarget member : Nat → Nat → Nat)
    (value parameter : Nat) : Nat :=
  iterateValue oldSource oldTarget member (payloadValue value + 1)
    (initialValue value parameter)

def finishedValue (state : Nat) : Nat :=
  if (Nat.unpair state).1 = 1 ∧ (Nat.unpair state).2 = 0 then 1 else 0

def validatorValue (oldSource oldTarget member : Nat → Nat → Nat)
    (value parameter : Nat) : Nat :=
  finishedValue (runValue oldSource oldTarget member value parameter)

/-- Concrete unary state selectors. The changing parameter is INSIDE each
frame, never a single external parameter shared by the entire traversal. -/
def status : Program 1 := InternalUnpair.left
def work : Program 1 := InternalUnpair.right
def currentFrame : Program 1 :=
  .composition InternalListCodec.headCode (fun _ : Fin 1 => work)
def rest : Program 1 :=
  .composition InternalListCodec.tailCode (fun _ : Fin 1 => work)
def currentRaw : Program 1 := leftOf currentFrame
def currentParameter : Program 1 := rightOf currentFrame
def currentType : Program 1 := leftOf currentRaw
def currentTag : Program 1 :=
  .composition OriginalLambdaConstructor.tag (fun _ : Fin 1 => currentRaw)
def currentDomain : Program 1 :=
  .composition OriginalLambdaConstructor.domain (fun _ : Fin 1 => currentRaw)
def currentFunction : Program 1 :=
  pairOf (consOf currentDomain currentType)
    (InternalApplicationStepPeel.functionPayload currentRaw)
def currentArgument : Program 1 :=
  pairOf currentDomain (InternalApplicationStepPeel.argumentPayload currentRaw)
def currentCodomain : Program 1 :=
  .composition InternalListCodec.tailCode (fun _ : Fin 1 => currentType)
def currentBody : Program 1 :=
  .composition OriginalLambdaConstructor.bodyCode ![currentCodomain,currentRaw]
def childParameter : Program 1 :=
  pairOf (leftOf currentParameter) (consOf currentDomain (rightOf currentParameter))

def exactOne {n : Nat} (p : Program n) : Program n :=
  InternalApplicationValidityStack.exactOne p

/-- This is an explicit PR AST, not an oracle for hereditary validity. -/
def nodeCheck (oldSource oldTarget member : Program 2) : Program 1 :=
  InternalAcceptance.conjunction
    (exactOne (.composition oldSource ![currentRaw,currentParameter]))
    (InternalAcceptance.conjunction
      (exactOne (.composition oldTarget ![currentRaw,currentParameter]))
      (InternalAcceptance.branch
        (InternalApplicationStepPeel.same currentTag (two 1))
        (InternalLessThan.constantOne 1)
        (exactOne (.composition member ![currentType,currentParameter]))))

def popped : Program 1 := pairOf (InternalLessThan.constantOne 1) rest

def applicationExpanded : Program 1 :=
  pairOf (InternalLessThan.constantOne 1)
    (consOf (pairOf currentFunction currentParameter)
      (consOf (pairOf currentArgument currentParameter) rest))

def lambdaExpanded : Program 1 :=
  pairOf (InternalLessThan.constantOne 1)
    (consOf (pairOf currentBody childParameter) rest)

/-- Every accepting visit uses the SAME explicit check before either
constructor expansion. Failure is literal zero, and accepted-empty is fixed. -/
def transition (oldSource oldTarget member : Program 2) : Program 1 :=
  InternalAcceptance.branch (exactOne status) (InternalAcceptance.constantZero 1)
    (InternalAcceptance.branch work (.projection 0)
      (InternalAcceptance.branch (exactOne (nodeCheck oldSource oldTarget member))
        (InternalAcceptance.constantZero 1)
        (InternalAcceptance.branch
          (InternalApplicationStepPeel.same currentTag (two 1))
          (InternalAcceptance.branch
            (InternalApplicationStepPeel.same currentTag (InternalLessThan.constantOne 1))
            popped lambdaExpanded)
          applicationExpanded)))

/-- Inputs [count,initial state]. The recursion index is ignored. -/
def iterate (oldSource oldTarget member : Program 2) : Program 2 :=
  .recursion (.projection (0 : Fin 1))
    (.composition (transition oldSource oldTarget member)
      (fun _ : Fin 1 => .projection (1 : Fin 3)))

/-- Inputs [original raw value,original runtime parameter]. Fuel is exactly
its term payload plus one, not a bound on the parameter or paired frame. -/
def fuel : Program 2 :=
  .composition .succ (fun _ : Fin 1 => rightOf (.projection 0))

def initial : Program 2 :=
  pairOf (InternalLessThan.constantOne 2)
    (consOf (pairOf (.projection 0) (.projection 1)) (InternalAcceptance.constantZero 2))

def run (oldSource oldTarget member : Program 2) : Program 2 :=
  .composition (iterate oldSource oldTarget member) ![fuel,initial]

def finished : Program 1 :=
  InternalAcceptance.conjunction (exactOne status)
    (InternalApplicationStepPeel.same work (InternalAcceptance.constantZero 1))

def validator (oldSource oldTarget member : Program 2) : Program 2 :=
  .composition finished (fun _ : Fin 1 => run oldSource oldTarget member)

/-- The guard captures precisely the oldSource, oldTarget and member leaves
of N = normalizeData (BottomParameter.baseData rawData). It never captures the
representative leaf or the eventual full application-only source fold. -/
def normalizedData (rawData : Data) : Data :=
  InternalOriginalUniformContextMembership.normalizeData (BottomParameter.baseData rawData)

def guard (rawData : Data) : Program 2 :=
  let N := normalizedData rawData
  validator N.oldSource N.oldTarget N.member

/-- Only the RAW source leaf changes. This does not assert calibration or
retain any Package. Later selection bottom-normalizes this conjunction, so
its source leaf is NOT definitionally N.oldSource conjoined with guard rawData.
An independent internal bottom-parameter invariance bridge remains pending. -/
def refineData (rawData : Data) : Data :=
  { rawData with oldSource := InternalAcceptance.conjunction rawData.oldSource (guard rawData) }

/-- Literal original lambda payload pair 1 (pair d bp). These shared graph
witnesses are arbitrary object-language terms, not a decoded typed lambda. -/
def lambdaPayloadWitnesses {alpha : Type}
    (payload middle d bp : OTerm alpha) : Formula alpha :=
  InternalPairingSumBounds.pairGraph payload
    (OrdinaryArithmetic.succTerm OrdinaryArithmetic.zeroTerm) middle ⊓
      InternalPairingSumBounds.pairGraph middle d bp

/- FIRST PACKET ONLY: the frozen targets concern the explicit machine,
its numeric calibration/measure, and original internal payload arithmetic.
Recursive guard laws, all-input redundancy under original calibration,
internal lambda-body closure, transport to the SAME final source Program,
and retention of the whole final Package are separate pending obligations. -/

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidity
