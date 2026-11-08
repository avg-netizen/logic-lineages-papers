module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStack
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph InternalGraphComposition
open InternalApplicationCertificateConstructors SourceComputabilityFormulaSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Work frames alone are new implementation data. Source term, pair and list
codes are unchanged. A visit retains the whole original packed input; a finish
retains the original application domain and result type, not child outputs. -/
def visitValue (value : Nat) : Nat := Nat.pair 0 value
def finishValue (domain codomain : Nat) : Nat := Nat.pair 1 (Nat.pair domain codomain)

structure State where
  status : Nat
  work : List Nat
  results : List Nat

def encodeState (state : State) : Nat :=
  Nat.pair state.status (Nat.pair (NumberedMultisetNumeric.numbersNumber state.work)
    (NumberedMultisetNumeric.numbersNumber state.results))

def failedState : State := ⟨0, [], []⟩

/-- Only an exact-one original root guard opens an application. Every other
visit pushes the WHOLE original packed input's leaf value. The function is
visited before the argument, so finish pops argument before function. -/
def stateStep (guard leaf : Nat → Nat) (combine : Nat → Nat → Nat → Nat → Nat)
    (state : State) : State :=
  if state.status = 1 then
    match state.work with
    | [] => state
    | frame :: rest =>
      let tag := (Nat.unpair frame).1
      let value := (Nat.unpair frame).2
      if tag = 0 then
        if InternalApplicationValidityStack.tagValue value = 2 ∧ guard value = 1 then
          ⟨1, visitValue (InternalApplicationValidityStack.functionChildValue value) ::
            visitValue (InternalApplicationValidityStack.argumentChildValue value) ::
            finishValue (InternalApplicationValidityStack.domainValue value)
              (InternalApplicationValidityStack.resultTypeValue value) :: rest, state.results⟩
        else ⟨1, rest, leaf value :: state.results⟩
      else if tag = 1 then
        match state.results with
        | argument :: function :: results =>
          ⟨1, rest, combine (Nat.unpair value).1 (Nat.unpair value).2 function argument :: results⟩
        | _ => failedState
      else failedState
  else failedState

/-- Direct total numeric execution, including malformed frame tags, every
non-one status, and insufficient result stacks. No decoding premise occurs. -/
def transitionValue (guard leaf : Nat → Nat) (combine : Nat → Nat → Nat → Nat → Nat)
    (state : Nat) : Nat :=
  if (Nat.unpair state).1 = 1 then
    let work := (Nat.unpair (Nat.unpair state).2).1
    let results := (Nat.unpair (Nat.unpair state).2).2
    if work = 0 then state else
      let frame := (Nat.unpair (work - 1)).1
      let rest := (Nat.unpair (work - 1)).2
      let tag := (Nat.unpair frame).1
      let value := (Nat.unpair frame).2
      if tag = 0 then
        if InternalApplicationValidityStack.tagValue value = 2 ∧ guard value = 1 then
          Nat.pair 1 (Nat.pair
            (1 + Nat.pair (visitValue (InternalApplicationValidityStack.functionChildValue value))
              (1 + Nat.pair (visitValue (InternalApplicationValidityStack.argumentChildValue value))
                (1 + Nat.pair (finishValue (InternalApplicationValidityStack.domainValue value)
                  (InternalApplicationValidityStack.resultTypeValue value)) rest))) results)
        else Nat.pair 1 (Nat.pair rest (1 + Nat.pair (leaf value) results))
      else if tag = 1 then
        if results = 0 then 0 else
          let afterArgument := (Nat.unpair (results - 1)).2
          if afterArgument = 0 then 0 else
            let argument := (Nat.unpair (results - 1)).1
            let function := (Nat.unpair (afterArgument - 1)).1
            let remaining := (Nat.unpair (afterArgument - 1)).2
            Nat.pair 1 (Nat.pair rest (1 + Nat.pair
              (combine (Nat.unpair value).1 (Nat.unpair value).2 function argument) remaining))
      else 0
  else 0

/-- Newly computed outputs may grow without bound. They contribute NOTHING to
this measure. Every non-visit frame, including a malformed one, costs one. -/
def frameWeight (frame : Nat) : Nat :=
  if (Nat.unpair frame).1 = 0 then
    2 * InternalApplicationValidityStack.payloadValue (Nat.unpair frame).2 + 1
  else 1

def workWeight (work : List Nat) : Nat := (work.map frameWeight).sum
def fuelValue (value : Nat) : Nat := 2 * InternalApplicationValidityStack.payloadValue value + 1

def headOf {n : Nat} (p : Program n) : Program n :=
  .composition InternalListCodec.headCode (fun _ : Fin 1 => p)
def tailOf {n : Nat} (p : Program n) : Program n :=
  .composition InternalListCodec.tailCode (fun _ : Fin 1 => p)
def visitOf {n : Nat} (p : Program n) : Program n :=
  pairOf (InternalAcceptance.constantZero n) p
def finishOf {n : Nat} (domain codomain : Program n) : Program n :=
  pairOf (InternalLessThan.constantOne n) (pairOf domain codomain)
def liveOf {n : Nat} (work results : Program n) : Program n :=
  pairOf (InternalLessThan.constantOne n) (pairOf work results)

def status : Program 1 := InternalUnpair.left
def work : Program 1 := leftOf InternalUnpair.right
def results : Program 1 := rightOf InternalUnpair.right
def currentFrame : Program 1 := headOf work
def rest : Program 1 := tailOf work
def frameTag : Program 1 := leftOf currentFrame
def currentValue : Program 1 := rightOf currentFrame
def currentDomain : Program 1 := InternalApplicationStepPeel.appDomain currentValue
def currentType : Program 1 := leftOf currentValue
def currentFunction : Program 1 :=
  pairOf (consOf currentDomain currentType)
    (InternalApplicationStepPeel.functionPayload currentValue)
def currentArgument : Program 1 :=
  pairOf currentDomain (InternalApplicationStepPeel.argumentPayload currentValue)

/-- Guard input is the original RAW ROOT, not its type, normalized value or
one of its children. The output is normalized to exactly zero or one. -/
def openGuard (guard : Program 1) : Program 1 :=
  InternalAcceptance.conjunction
    (InternalApplicationStepPeel.same
      (InternalApplicationStepPeel.constructorTag (.projection 0)) (two 1)) guard

def expanded : Program 1 := liveOf
  (consOf (visitOf currentFunction)
    (consOf (visitOf currentArgument) (consOf (finishOf currentDomain currentType) rest))) results

def leafReturned (leaf : Program 1) : Program 1 :=
  liveOf rest (consOf (.composition leaf (fun _ : Fin 1 => currentValue)) results)

/-- Combine inputs are exactly [domain,codomain,functionOutput,argumentOutput]. -/
def combined (combine : Program 4) : Program 1 :=
  .composition combine ![leftOf currentValue,rightOf currentValue,
    headOf (tailOf results),headOf results]

def finishReturned (combine : Program 4) : Program 1 :=
  liveOf rest (consOf (combined combine) (tailOf (tailOf results)))

/-- A concrete finite original PR AST. No representability witness, semantic
oracle, derivability field or recursive application equation is assumed. -/
def transition (guard leaf : Program 1) (combine : Program 4) : Program 1 :=
  InternalAcceptance.branch (InternalApplicationValidityStack.exactOne status)
    (InternalAcceptance.constantZero 1)
    (InternalAcceptance.branch work (.projection 0)
      (InternalAcceptance.branch
        (InternalApplicationStepPeel.same frameTag (InternalAcceptance.constantZero 1))
        (InternalAcceptance.branch (InternalApplicationValidityStack.exactOne frameTag)
          (InternalAcceptance.constantZero 1)
          (InternalAcceptance.branch results (InternalAcceptance.constantZero 1)
            (InternalAcceptance.branch (tailOf results) (InternalAcceptance.constantZero 1)
              (finishReturned combine))))
        (InternalAcceptance.branch
          (.composition (openGuard guard) (fun _ : Fin 1 => currentValue))
          (leafReturned leaf) expanded)))

/-- Inputs [count,initial]. Only the preceding computed state is passed to
the transition. This is ordinary numeric recursion, not raw-list recursion. -/
def iterate (guard leaf : Program 1) (combine : Program 4) : Program 2 :=
  .recursion (.projection (0 : Fin 1))
    (.composition (transition guard leaf combine) (fun _ : Fin 1 => .projection (1 : Fin 3)))

/-- Exactly 2*payload+1. Neither the packed type nor any output contributes. -/
def fuel : Program 1 :=
  .composition .succ (fun _ : Fin 1 =>
    .composition InternalArithmeticPrograms.addition ![InternalUnpair.right,InternalUnpair.right])
def initial : Program 1 := liveOf
  (consOf (visitOf (.projection 0)) (InternalAcceptance.constantZero 1))
  (InternalAcceptance.constantZero 1)
def run (guard leaf : Program 1) (combine : Program 4) : Program 1 :=
  .composition (iterate guard leaf combine) ![fuel,initial]

/-- Only a live, empty-work state with EXACTLY one result returns that result.
No theorem in this first packet claims that all initial runs have this shape. -/
def output : Program 1 :=
  InternalAcceptance.branch (InternalApplicationValidityStack.exactOne status)
    (InternalAcceptance.constantZero 1)
    (InternalAcceptance.branch work
      (InternalAcceptance.branch results (InternalAcceptance.constantZero 1)
        (InternalAcceptance.branch (tailOf results) (headOf results)
          (InternalAcceptance.constantZero 1)))
      (InternalAcceptance.constantZero 1))

/-- The bounded result-producing AST is exposed concretely. Its recursive
fold equation, result-stack preservation and representative calibration are
separate, still pending obligations, not supplied by the one-step packet. -/
def fold (guard leaf : Program 1) (combine : Program 4) : Program 1 :=
  .composition output (fun _ : Fin 1 => run guard leaf combine)

/-- Exact constructor inputs [rawValue,workSuffix,resultStack]. -/
def visitState : Program 3 :=
  liveOf (consOf (visitOf (.projection 0)) (.projection 1)) (.projection 2)

/-- Exact constructor inputs [result,workSuffix,resultStack]. -/
def returnState : Program 3 :=
  liveOf (.projection 1) (consOf (.projection 0) (.projection 2))

/-- A completed worklist preserves the arbitrary whole result stack. -/
def emptyState : Program 1 := liveOf (InternalAcceptance.constantZero 1) (.projection 0)

/-- Inputs [domain,codomain,functionPayload,argumentPayload,workSuffix,results]. -/
def expandedState : Program 6 := liveOf
  (consOf (visitOf (pairOf (consOf (.projection 0) (.projection 1)) (.projection 2)))
    (consOf (visitOf (pairOf (.projection 0) (.projection 3)))
      (consOf (finishOf (.projection 0) (.projection 1)) (.projection 4)))) (.projection 5)

/-- Inputs [domain,codomain,workSuffix,argumentOutput,functionOutput,resultSuffix]. -/
def finishState : Program 6 := liveOf
  (consOf (finishOf (.projection 0) (.projection 1)) (.projection 2))
  (consOf (.projection 3) (consOf (.projection 4) (.projection 5)))

abbrev graph6 {α : Type} (p : Program 6) (out a b c d e f : OTerm α) : Formula α :=
  programGraph p out (Fin.cons a (Fin.cons b (Fin.cons c
    (Fin.cons d (Fin.cons e (Fin.cons f Fin.elim0))))))

/-- The actual leaf output is quantified internally rather than supplied as a
semantic value. All work and result suffixes are arbitrary symbolic codes. -/
def leafResult {α : Type} (leaf : Program 1) (out value work results : OTerm α) : Formula α :=
  existsOne
    (graph1 leaf (.var (.inr (0 : Fin 1))) (value.relabel Sum.inl) ⊓
      graph3 returnState (out.relabel Sum.inl) (.var (.inr (0 : Fin 1)))
        (work.relabel Sum.inl) (results.relabel Sum.inl))

/-- The two prior outputs remain in their ORIGINAL function/argument order
when passed to combine, although the result stack stores argument first. -/
def finishResult {α : Type} (combine : Program 4)
    (out domain codomain work argument function results : OTerm α) : Formula α :=
  existsOne
    (graph4 combine (.var (.inr (0 : Fin 1))) (domain.relabel Sum.inl)
        (codomain.relabel Sum.inl) (function.relabel Sum.inl) (argument.relabel Sum.inl) ⊓
      graph3 returnState (out.relabel Sum.inl) (.var (.inr (0 : Fin 1)))
        (work.relabel Sum.inl) (results.relabel Sum.inl))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStack
