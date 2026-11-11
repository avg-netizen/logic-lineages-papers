module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversal
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Machine frames only. Every visit carries its own ORIGINAL runtime
parameter. Return frames retain original domain/codomain numbers, not a
decoded context, a canonical output or an encoded source term. -/
def visitValue (value parameter : Nat) : Nat := Nat.pair 0 (Nat.pair value parameter)
def applicationReturnValue (domain codomain : Nat) : Nat := Nat.pair 1 (Nat.pair domain codomain)
def lambdaReturnValue (domain codomain : Nat) : Nat := Nat.pair 2 (Nat.pair domain codomain)

abbrev State := InternalApplicationResultStack.State
abbrev encodeState := InternalApplicationResultStack.encodeState
abbrev failedState := InternalApplicationResultStack.failedState
abbrev payloadValue := OriginalHereditaryValidity.payloadValue
abbrev resultTypeValue := OriginalHereditaryValidity.resultTypeValue
abbrev tagValue := OriginalHereditaryValidity.tagValue
abbrev domainValue := OriginalHereditaryValidity.domainValue
abbrev functionChildValue := OriginalHereditaryValidity.functionChildValue
abbrev argumentChildValue := OriginalHereditaryValidity.argumentChildValue
abbrev lambdaCodomainValue := OriginalHereditaryValidity.lambdaCodomainValue
abbrev lambdaBodyValue := OriginalHereditaryValidity.lambdaBodyValue
abbrev childParameterValue := OriginalHereditaryValidity.childParameterValue

/-- Literal original constructor numbers. Only the outer type fields of
computed children are discarded, just as in the accepted original ASTs. -/
def applicationValue (domain codomain function argument : Nat) : Nat :=
  Nat.pair codomain (Nat.pair 2 (Nat.pair domain
    (Nat.pair (Nat.unpair function).2 (Nat.unpair argument).2)))

def lambdaValue (domain codomain body : Nat) : Nat :=
  Nat.pair (1 + Nat.pair domain codomain)
    (Nat.pair 1 (Nat.pair domain (Nat.unpair body).2))

/-- Every literal application and lambda opens. Only OTHER term tags use
the selected leaf. This raw machine alone is not a representative on invalid
inputs: its separately specified active wrapper retains original fallback. -/
def stateStep (leaf : Nat → Nat → Nat) (state : State) : State :=
  if state.status = 1 then
    match state.work with
    | [] => state
    | frame :: rest =>
      let tag := (Nat.unpair frame).1
      let payload := (Nat.unpair frame).2
      if tag = 0 then
        let value := (Nat.unpair payload).1
        let parameter := (Nat.unpair payload).2
        if tagValue value = 2 then
          ⟨1, visitValue (functionChildValue value) parameter ::
            visitValue (argumentChildValue value) parameter ::
            applicationReturnValue (domainValue value) (resultTypeValue value) :: rest,
            state.results⟩
        else if tagValue value = 1 then
          ⟨1, visitValue (lambdaBodyValue value) (childParameterValue value parameter) ::
            lambdaReturnValue (domainValue value) (lambdaCodomainValue value) :: rest,
            state.results⟩
        else ⟨1, rest, leaf value parameter :: state.results⟩
      else if tag = 1 then
        match state.results with
        | argument :: function :: results =>
          ⟨1, rest, applicationValue (Nat.unpair payload).1 (Nat.unpair payload).2
            function argument :: results⟩
        | _ => failedState
      else if tag = 2 then
        match state.results with
        | body :: results =>
          ⟨1, rest, lambdaValue (Nat.unpair payload).1 (Nat.unpair payload).2 body :: results⟩
        | _ => failedState
      else failedState
  else failedState

/-- Direct execution at EVERY raw state. Non-one status, unknown frame tag
and insufficient result stacks fail at literal zero. No decoding, validity,
Boolean-leaf or source-universe premise restricts this total function. -/
def transitionValue (leaf : Nat → Nat → Nat) (state : Nat) : Nat :=
  if (Nat.unpair state).1 = 1 then
    let work := (Nat.unpair (Nat.unpair state).2).1
    let results := (Nat.unpair (Nat.unpair state).2).2
    if work = 0 then state else
      let frame := (Nat.unpair (work - 1)).1
      let rest := (Nat.unpair (work - 1)).2
      let tag := (Nat.unpair frame).1
      let payload := (Nat.unpair frame).2
      if tag = 0 then
        let value := (Nat.unpair payload).1
        let parameter := (Nat.unpair payload).2
        if tagValue value = 2 then
          Nat.pair 1 (Nat.pair
            (1 + Nat.pair (visitValue (functionChildValue value) parameter)
              (1 + Nat.pair (visitValue (argumentChildValue value) parameter)
                (1 + Nat.pair (applicationReturnValue (domainValue value)
                  (resultTypeValue value)) rest))) results)
        else if tagValue value = 1 then
          Nat.pair 1 (Nat.pair
            (1 + Nat.pair (visitValue (lambdaBodyValue value)
              (childParameterValue value parameter))
              (1 + Nat.pair (lambdaReturnValue (domainValue value)
                (lambdaCodomainValue value)) rest)) results)
        else Nat.pair 1 (Nat.pair rest (1 + Nat.pair (leaf value parameter) results))
      else if tag = 1 then
        if results = 0 then 0 else
          let afterArgument := (Nat.unpair (results - 1)).2
          if afterArgument = 0 then 0 else
            let argument := (Nat.unpair (results - 1)).1
            let function := (Nat.unpair (afterArgument - 1)).1
            let remaining := (Nat.unpair (afterArgument - 1)).2
            Nat.pair 1 (Nat.pair rest (1 + Nat.pair
              (applicationValue (Nat.unpair payload).1 (Nat.unpair payload).2
                function argument) remaining))
      else if tag = 2 then
        if results = 0 then 0 else
          Nat.pair 1 (Nat.pair rest (1 + Nat.pair
            (lambdaValue (Nat.unpair payload).1 (Nat.unpair payload).2
              (Nat.unpair (results - 1)).1)
            (Nat.unpair (results - 1)).2))
      else 0
  else 0

/-- Only ORIGINAL input payloads determine the budget. Parameters, packed
types and newly computed outputs may grow arbitrarily. Every return or
malformed non-visit frame has unit cost. -/
def frameWeight (frame : Nat) : Nat :=
  if (Nat.unpair frame).1 = 0 then
    2 * payloadValue (Nat.unpair (Nat.unpair frame).2).1 + 1
  else 1

def workWeight (work : List Nat) : Nat := (work.map frameWeight).sum
def fuelValue (value : Nat) : Nat := 2 * payloadValue value + 1
def initialValue (value parameter : Nat) : Nat :=
  Nat.pair 1 (Nat.pair (1 + Nat.pair (visitValue value parameter) 0) 0)

def iterateValue (leaf : Nat → Nat → Nat) (count initial : Nat) : Nat :=
  Nat.rec initial (fun _ state => transitionValue leaf state) count

def runValue (leaf : Nat → Nat → Nat) (value parameter : Nat) : Nat :=
  iterateValue leaf (fuelValue value) (initialValue value parameter)

/-- Exactly one result is required. A malformed/nonterminal state returns
zero, including live empty work with no results or more than one result. -/
def outputValue (state : Nat) : Nat :=
  let work := (Nat.unpair (Nat.unpair state).2).1
  let results := (Nat.unpair (Nat.unpair state).2).2
  if (Nat.unpair state).1 = 1 ∧ work = 0 ∧ results ≠ 0 ∧
      (Nat.unpair (results - 1)).2 = 0 then (Nat.unpair (results - 1)).1 else 0

def foldValue (leaf : Nat → Nat → Nat) (value parameter : Nat) : Nat :=
  outputValue (runValue leaf value parameter)

abbrev headOf {n : Nat} (p : Program n) : Program n := InternalApplicationResultStack.headOf p
abbrev tailOf {n : Nat} (p : Program n) : Program n := InternalApplicationResultStack.tailOf p
abbrev liveOf {n : Nat} (work results : Program n) : Program n :=
  InternalApplicationResultStack.liveOf work results

def visitOf {n : Nat} (value parameter : Program n) : Program n :=
  pairOf (InternalAcceptance.constantZero n) (pairOf value parameter)
def applicationReturnOf {n : Nat} (domain codomain : Program n) : Program n :=
  pairOf (InternalLessThan.constantOne n) (pairOf domain codomain)
def lambdaReturnOf {n : Nat} (domain codomain : Program n) : Program n :=
  pairOf (two n) (pairOf domain codomain)

abbrev status := InternalApplicationResultStack.status
abbrev work := InternalApplicationResultStack.work
abbrev results := InternalApplicationResultStack.results
abbrev currentFrame := InternalApplicationResultStack.currentFrame
abbrev rest := InternalApplicationResultStack.rest
abbrev frameTag := InternalApplicationResultStack.frameTag
def framePayload : Program 1 := rightOf currentFrame
def currentRaw : Program 1 := leftOf framePayload
def currentParameter : Program 1 := rightOf framePayload

/-- Total ORIGINAL raw selectors. No typed decoding is performed. -/
def rawType : Program 1 := InternalUnpair.left
def rawTag : Program 1 := OriginalLambdaConstructor.tag
def rawDomain : Program 1 := OriginalLambdaConstructor.domain
def rawFunction : Program 1 :=
  pairOf (consOf rawDomain rawType)
    (InternalApplicationStepPeel.functionPayload (.projection 0))
def rawArgument : Program 1 :=
  pairOf rawDomain (InternalApplicationStepPeel.argumentPayload (.projection 0))
def rawCodomain : Program 1 := tailOf rawType
def rawBody : Program 1 :=
  .composition OriginalLambdaConstructor.bodyCode ![rawCodomain,.projection 0]

/-- Inputs [raw value,parameter]. The ACTUAL payload domain is consed onto
the original Encodable Gamma code. The outer context is retained literally;
typesNumber Gamma is never substituted for that runtime code. -/
def childParameter : Program 2 :=
  pairOf (leftOf (.projection 1))
    (consOf (.composition rawDomain (fun _ : Fin 1 => .projection 0))
      (rightOf (.projection 1)))

def currentTag : Program 1 := .composition rawTag (fun _ : Fin 1 => currentRaw)
def currentDomain : Program 1 := .composition rawDomain (fun _ : Fin 1 => currentRaw)
def currentType : Program 1 := .composition rawType (fun _ : Fin 1 => currentRaw)
def currentFunction : Program 1 := .composition rawFunction (fun _ : Fin 1 => currentRaw)
def currentArgument : Program 1 := .composition rawArgument (fun _ : Fin 1 => currentRaw)
def currentCodomain : Program 1 := .composition rawCodomain (fun _ : Fin 1 => currentRaw)
def currentBody : Program 1 := .composition rawBody (fun _ : Fin 1 => currentRaw)
def currentChildParameter : Program 1 := .composition childParameter ![currentRaw,currentParameter]

def applicationExpanded : Program 1 := liveOf
  (consOf (visitOf currentFunction currentParameter)
    (consOf (visitOf currentArgument currentParameter)
      (consOf (applicationReturnOf currentDomain currentType) rest))) results

def lambdaExpanded : Program 1 := liveOf
  (consOf (visitOf currentBody currentChildParameter)
    (consOf (lambdaReturnOf currentDomain currentCodomain) rest)) results

def leafReturned (leaf : Program 2) : Program 1 :=
  liveOf rest (consOf (.composition leaf ![currentRaw,currentParameter]) results)

def applicationReturned : Program 1 := liveOf rest
  (consOf (.composition application
    ![leftOf framePayload,rightOf framePayload,headOf (tailOf results),headOf results])
    (tailOf (tailOf results)))

def lambdaReturned : Program 1 := liveOf rest
  (consOf (.composition OriginalLambdaConstructor.constructor
    ![leftOf framePayload,rightOf framePayload,headOf results]) (tailOf results))

/-- Explicit unary PR transition. Guardless structural visits do not assert
source validity. Failure and underflow branches remain total on raw states. -/
def transition (leaf : Program 2) : Program 1 :=
  InternalAcceptance.branch (OriginalHereditaryValidity.exactOne status)
    (InternalAcceptance.constantZero 1)
    (InternalAcceptance.branch work (.projection 0)
      (InternalAcceptance.branch
        (InternalApplicationStepPeel.same frameTag (InternalAcceptance.constantZero 1))
        (InternalAcceptance.branch (OriginalHereditaryValidity.exactOne frameTag)
          (InternalAcceptance.branch
            (InternalApplicationStepPeel.same frameTag (two 1))
            (InternalAcceptance.constantZero 1)
            (InternalAcceptance.branch results (InternalAcceptance.constantZero 1) lambdaReturned))
          (InternalAcceptance.branch results (InternalAcceptance.constantZero 1)
            (InternalAcceptance.branch (tailOf results) (InternalAcceptance.constantZero 1)
              applicationReturned)))
        (InternalAcceptance.branch
          (InternalApplicationStepPeel.same currentTag (two 1))
          (InternalAcceptance.branch (OriginalHereditaryValidity.exactOne currentTag)
            (leafReturned leaf) lambdaExpanded)
          applicationExpanded)))

/-- Inputs [count,initial]. No externally fixed parameter is threaded through
the iterator: every visit reads the parameter stored in its own frame. -/
def iterate (leaf : Program 2) : Program 2 :=
  .recursion (.projection (0 : Fin 1))
    (.composition (transition leaf) (fun _ : Fin 1 => .projection (1 : Fin 3)))

def fuel : Program 2 :=
  .composition InternalApplicationResultStack.fuel (fun _ : Fin 1 => .projection 0)
def initial : Program 2 := liveOf
  (consOf (visitOf (.projection 0) (.projection 1)) (InternalAcceptance.constantZero 2))
  (InternalAcceptance.constantZero 2)
def run (leaf : Program 2) : Program 2 := .composition (iterate leaf) ![fuel,initial]
abbrev output := InternalApplicationResultStack.output
def fold (leaf : Program 2) : Program 2 := .composition output (fun _ : Fin 1 => run leaf)

/- FOUNDATION ONLY. All-input native machine calibration, termination and
internal recurrence are separate proof obligations. This definition supplies
no canonicality, semantic reflection, final-source replacement or Package. -/

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversal
