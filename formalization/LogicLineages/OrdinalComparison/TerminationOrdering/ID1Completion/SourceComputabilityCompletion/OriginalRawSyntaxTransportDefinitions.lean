module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliarySubstitutionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedVariableCountDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransport
open Source NumberedAuxiliaryCoding NumberedRewriteSyntax NumberedRewriteReduction
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- These modes select three concrete finite Program ASTs, not an oracle or a
representability witness. Rank counts ALL variable occurrences, including bound
ones; it is neither a free-variable count nor a maximum variable index. -/
inductive Mode where
  | shift | erase | rank
  deriving DecidableEq

/-- Literal cutoff erasure on the ORIGINAL eight-constructor auxiliary syntax.
The erased variable's type is retained under binders; only the cutoff changes. -/
def eraseCode {Symbol : Type} (erasedType : Ty) (cutoff : Nat) : Code Symbol → Code Symbol
  | .var i => if i < cutoff then .var i else if i = cutoff then .bottom erasedType else .var (i - 1)
  | .lam sigma body => .lam sigma (eraseCode erasedType (cutoff + 1) body)
  | .app sigma q a => .app sigma (eraseCode erasedType cutoff q) (eraseCode erasedType cutoff a)
  | .bottom tau => .bottom tau
  | .ordinary head base => .ordinary head (eraseCode erasedType cutoff base)
  | .numbered label head tau base types extras =>
      .numbered label head tau (eraseCode erasedType cutoff base) types (eraseCode erasedType cutoff extras)
  | .argumentsNil => .argumentsNil
  | .argumentsCons sigma q rest =>
      .argumentsCons sigma (eraseCode erasedType cutoff q) (eraseCode erasedType cutoff rest)

def codeVariableCount {Symbol : Type} : Code Symbol → Nat
  | .var _ => 1
  | .lam _ body => codeVariableCount body
  | .app _ q a => codeVariableCount q + codeVariableCount a
  | .bottom _ => 0
  | .ordinary _ base => codeVariableCount base
  | .numbered _ _ _ base _ extras => codeVariableCount base + codeVariableCount extras
  | .argumentsNil => 0
  | .argumentsCons _ q rest => codeVariableCount q + codeVariableCount rest

/-- Lift the existing single-bottom substitution through exactly the protected
binder prefix. No source type-window membership is assumed or introduced. -/
def prefixErasure {Symbol : Type} {arity : Symbol → Nat} (binders Gamma : List Ty) (sigma : Ty) :
    NumberedRewriteSyntax.Substitution Symbol arity (binders ++ sigma :: Gamma) (binders ++ Gamma) :=
  match binders with
  | [] => singleSubstitution (.bottom sigma)
  | _ :: rest => liftSubstitution (prefixErasure rest Gamma sigma)

abbrev State := InternalApplicationResultStack.State
abbrev encodeState := InternalApplicationResultStack.encodeState
abbrev failedState := InternalApplicationResultStack.failedState

def tagValue (raw : Nat) : Nat := (Nat.unpair raw).1
def payloadValue (raw : Nat) : Nat := (Nat.unpair raw).2

/-- Raw tags 1/4 have one child, tags 2/5/7 have two. All other tags are
leaves, including malformed tag-six payloads and unknown tags greater than 7. -/
def arityValue (raw : Nat) : Nat :=
  if tagValue raw = 1 ∨ tagValue raw = 4 then 1
  else if tagValue raw = 2 ∨ tagValue raw = 5 ∨ tagValue raw = 7 then 2 else 0

def firstValue (raw : Nat) : Nat :=
  let p := payloadValue raw
  if tagValue raw = 1 ∨ tagValue raw = 4 then (Nat.unpair p).2
  else if tagValue raw = 5 then (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair p).2).2).2).1
  else (Nat.unpair (Nat.unpair p).2).1

def secondValue (raw : Nat) : Nat :=
  let p := payloadValue raw
  if tagValue raw = 5 then (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair p).2).2).2).2).2
  else (Nat.unpair (Nat.unpair p).2).2

def leafValue (mode : Mode) (erasedType cutoff raw : Nat) : Nat :=
  match mode with
  | .rank => if tagValue raw = 0 then 1 else 0
  | .shift => if tagValue raw = 0 then
      Nat.pair 0 (if payloadValue raw < cutoff then payloadValue raw else payloadValue raw + 1)
      else raw
  | .erase => if tagValue raw = 0 then
      if payloadValue raw < cutoff then raw
      else if payloadValue raw = cutoff then Nat.pair 3 erasedType
      else Nat.pair 0 (payloadValue raw - 1)
      else raw

/-- Metadata are copied literally, without decoding types, heads, labels or
extra-type lists. Child order is first-before-second, including base/extras. -/
def rebuildValue (mode : Mode) (raw first second : Nat) : Nat :=
  if mode = .rank then if arityValue raw = 1 then first else first + second
  else
    let p := payloadValue raw
    if tagValue raw = 1 then Nat.pair 1 (Nat.pair (Nat.unpair p).1 first)
    else if tagValue raw = 2 then Nat.pair 2 (Nat.pair (Nat.unpair p).1 (Nat.pair first second))
    else if tagValue raw = 4 then Nat.pair 4 (Nat.pair (Nat.unpair p).1 first)
    else if tagValue raw = 5 then Nat.pair 5
      (Nat.pair (Nat.unpair p).1 (Nat.pair (Nat.unpair (Nat.unpair p).2).1
        (Nat.pair (Nat.unpair (Nat.unpair (Nat.unpair p).2).2).1
          (Nat.pair first (Nat.pair (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair p).2).2).2).2).1 second)))))
    else if tagValue raw = 7 then Nat.pair 7 (Nat.pair (Nat.unpair p).1 (Nat.pair first second))
    else raw

/-- Machine frames only: visit = pair 0 (pair erasedType (pair cutoff raw));
return = pair 1 raw. The original raw payload is never mistaken for packedNumber. -/
def visitValue (erasedType cutoff raw : Nat) : Nat := Nat.pair 0 (Nat.pair erasedType (Nat.pair cutoff raw))
def finishValue (raw : Nat) : Nat := Nat.pair 1 raw

def stateStep (mode : Mode) (state : State) : State :=
  if state.status = 1 then
    match state.work with
    | [] => state
    | frame :: rest =>
      let tag := (Nat.unpair frame).1
      let p := (Nat.unpair frame).2
      if tag = 0 then
        let d := (Nat.unpair p).1
        let k := (Nat.unpair (Nat.unpair p).2).1
        let raw := (Nat.unpair (Nat.unpair p).2).2
        if arityValue raw = 1 then
          let childCutoff := if tagValue raw = 1 then k + 1 else k
          ⟨1, visitValue d childCutoff (firstValue raw) :: finishValue raw :: rest, state.results⟩
        else if arityValue raw = 2 then
          ⟨1, visitValue d k (firstValue raw) :: visitValue d k (secondValue raw) :: finishValue raw :: rest, state.results⟩
        else ⟨1, rest, leafValue mode d k raw :: state.results⟩
      else if tag = 1 then
        if arityValue p = 1 then
          match state.results with
          | first :: results => ⟨1, rest, rebuildValue mode p first 0 :: results⟩
          | _ => failedState
        else if arityValue p = 2 then
          match state.results with
          | second :: first :: results => ⟨1, rest, rebuildValue mode p first second :: results⟩
          | _ => failedState
        else failedState
      else failedState
  else failedState

/-- Independent direct numeric execution at every raw state. Non-one status,
unknown frames, returns for leaf tags and stack underflow all return zero. -/
def transitionValue (mode : Mode) (state : Nat) : Nat :=
  if (Nat.unpair state).1 = 1 then
    let work := (Nat.unpair (Nat.unpair state).2).1
    let results := (Nat.unpair (Nat.unpair state).2).2
    if work = 0 then state else
      let frame := (Nat.unpair (work - 1)).1
      let rest := (Nat.unpair (work - 1)).2
      let tag := (Nat.unpair frame).1
      let p := (Nat.unpair frame).2
      if tag = 0 then
        let d := (Nat.unpair p).1
        let k := (Nat.unpair (Nat.unpair p).2).1
        let raw := (Nat.unpair (Nat.unpair p).2).2
        if arityValue raw = 1 then
          let childCutoff := if tagValue raw = 1 then k + 1 else k
          Nat.pair 1 (Nat.pair
            (1 + Nat.pair (visitValue d childCutoff (firstValue raw))
              (1 + Nat.pair (finishValue raw) rest)) results)
        else if arityValue raw = 2 then
          Nat.pair 1 (Nat.pair
            (1 + Nat.pair (visitValue d k (firstValue raw))
              (1 + Nat.pair (visitValue d k (secondValue raw))
                (1 + Nat.pair (finishValue raw) rest))) results)
        else Nat.pair 1 (Nat.pair rest (1 + Nat.pair (leafValue mode d k raw) results))
      else if tag = 1 then
        if arityValue p = 1 then
          if results = 0 then 0 else
            Nat.pair 1 (Nat.pair rest (1 + Nat.pair
              (rebuildValue mode p (Nat.unpair (results - 1)).1 0) (Nat.unpair (results - 1)).2))
        else if arityValue p = 2 then
          if results = 0 then 0 else
            let afterSecond := (Nat.unpair (results - 1)).2
            if afterSecond = 0 then 0 else
              Nat.pair 1 (Nat.pair rest (1 + Nat.pair
                (rebuildValue mode p (Nat.unpair (afterSecond - 1)).1 (Nat.unpair (results - 1)).1)
                (Nat.unpair (afterSecond - 1)).2))
        else 0
      else 0
  else 0

def frameWeight (frame : Nat) : Nat :=
  if (Nat.unpair frame).1 = 0 then
    2 * (Nat.unpair (Nat.unpair (Nat.unpair frame).2).2).2 + 1 else 1

def workWeight (work : List Nat) : Nat := (work.map frameWeight).sum
def fuelValue (raw : Nat) : Nat := 2 * raw + 1
def initialValue (d k raw : Nat) : Nat := Nat.pair 1 (Nat.pair (1 + Nat.pair (visitValue d k raw) 0) 0)
def iterateValue (mode : Mode) (count initial : Nat) : Nat := Nat.rec initial (fun _ state => transitionValue mode state) count
def runValue (mode : Mode) (d k raw : Nat) : Nat := iterateValue mode (fuelValue raw) (initialValue d k raw)

def outputValue (state : Nat) : Nat :=
  let work := (Nat.unpair (Nat.unpair state).2).1
  let results := (Nat.unpair (Nat.unpair state).2).2
  if (Nat.unpair state).1 = 1 ∧ work = 0 ∧ results ≠ 0 ∧ (Nat.unpair (results - 1)).2 = 0
  then (Nat.unpair (results - 1)).1 else 0

def foldValue (mode : Mode) (d k raw : Nat) : Nat := outputValue (runValue mode d k raw)

/-- Finite numeral AST construction, with no external program selection. -/
def constant (n : Nat) : Nat → Program n
  | 0 => InternalAcceptance.constantZero n
  | k + 1 => .composition .succ (fun _ : Fin 1 => constant n k)
def succOf {n : Nat} (p : Program n) : Program n := .composition .succ (fun _ : Fin 1 => p)
def addOf {n : Nat} (p q : Program n) : Program n := .composition InternalArithmeticPrograms.addition ![p,q]
def sameOf {n : Nat} (p q : Program n) : Program n := InternalApplicationStepPeel.same p q

def rawTag : Program 1 := InternalUnpair.left
def rawPayload : Program 1 := InternalUnpair.right

def arityOf {n : Nat} (raw : Program n) : Program n :=
  InternalAcceptance.branch (sameOf (leftOf raw) (constant n 1))
    (InternalAcceptance.branch (sameOf (leftOf raw) (constant n 4))
      (InternalAcceptance.branch (sameOf (leftOf raw) (constant n 2))
        (InternalAcceptance.branch (sameOf (leftOf raw) (constant n 5))
          (InternalAcceptance.branch (sameOf (leftOf raw) (constant n 7)) (constant n 0) (constant n 2))
          (constant n 2)) (constant n 2)) (constant n 1)) (constant n 1)

def firstOf {n : Nat} (raw : Program n) : Program n :=
  let p := rightOf raw
  InternalAcceptance.branch (sameOf (leftOf raw) (constant n 1))
    (InternalAcceptance.branch (sameOf (leftOf raw) (constant n 4))
      (InternalAcceptance.branch (sameOf (leftOf raw) (constant n 5))
        (leftOf (rightOf p)) (leftOf (rightOf (rightOf (rightOf p)))))
      (rightOf p)) (rightOf p)

def secondOf {n : Nat} (raw : Program n) : Program n :=
  let p := rightOf raw
  InternalAcceptance.branch (sameOf (leftOf raw) (constant n 5))
    (rightOf (rightOf p)) (rightOf (rightOf (rightOf (rightOf (rightOf p)))))

/-- Inputs [erased type number, cutoff, raw codeNumber]. -/
def leaf (mode : Mode) : Program 3 :=
  let d : Program 3 := .projection 0
  let k : Program 3 := .projection 1
  let raw : Program 3 := .projection 2
  let i := rightOf raw
  let below := .composition InternalLessThan.ltTest ![i,k]
  match mode with
  | .rank => InternalAcceptance.branch (sameOf (leftOf raw) (constant 3 0)) (constant 3 0) (constant 3 1)
  | .shift => InternalAcceptance.branch (sameOf (leftOf raw) (constant 3 0)) raw
      (pairOf (constant 3 0) (InternalAcceptance.branch below (succOf i) i))
  | .erase => InternalAcceptance.branch (sameOf (leftOf raw) (constant 3 0)) raw
      (InternalAcceptance.branch below
        (InternalAcceptance.branch (sameOf i k)
          (pairOf (constant 3 0) (.composition InternalEqualityTest.predecessor (fun _ : Fin 1 => i)))
          (pairOf (constant 3 3) d)) raw)

/-- Inputs [original raw codeNumber, first output, second output]. -/
def rebuild (mode : Mode) : Program 3 :=
  let raw : Program 3 := .projection 0
  let first : Program 3 := .projection 1
  let second : Program 3 := .projection 2
  let p := rightOf raw
  match mode with
  | .rank => InternalAcceptance.branch (sameOf (arityOf raw) (constant 3 1)) (addOf first second) first
  | .shift | .erase =>
      InternalAcceptance.branch (sameOf (leftOf raw) (constant 3 1))
        (InternalAcceptance.branch (sameOf (leftOf raw) (constant 3 2))
          (InternalAcceptance.branch (sameOf (leftOf raw) (constant 3 4))
            (InternalAcceptance.branch (sameOf (leftOf raw) (constant 3 5))
              (InternalAcceptance.branch (sameOf (leftOf raw) (constant 3 7)) raw
                (pairOf (constant 3 7) (pairOf (leftOf p) (pairOf first second))))
              (pairOf (constant 3 5) (pairOf (leftOf p) (pairOf (leftOf (rightOf p))
                (pairOf (leftOf (rightOf (rightOf p))) (pairOf first
                  (pairOf (leftOf (rightOf (rightOf (rightOf (rightOf p))))) second)))))))
            (pairOf (constant 3 4) (pairOf (leftOf p) first)))
          (pairOf (constant 3 2) (pairOf (leftOf p) (pairOf first second))))
        (pairOf (constant 3 1) (pairOf (leftOf p) first))

def visitOf {n : Nat} (d k raw : Program n) : Program n := pairOf (constant n 0) (pairOf d (pairOf k raw))
def finishOf {n : Nat} (raw : Program n) : Program n := pairOf (constant n 1) raw
abbrev headOf {n : Nat} (p : Program n) : Program n := InternalApplicationResultStack.headOf p
abbrev tailOf {n : Nat} (p : Program n) : Program n := InternalApplicationResultStack.tailOf p
abbrev liveOf {n : Nat} (work results : Program n) : Program n := InternalApplicationResultStack.liveOf work results
abbrev status := InternalApplicationResultStack.status
abbrev work := InternalApplicationResultStack.work
abbrev results := InternalApplicationResultStack.results
abbrev frame := InternalApplicationResultStack.currentFrame
abbrev rest := InternalApplicationResultStack.rest
def frameTag : Program 1 := leftOf frame
def framePayload : Program 1 := rightOf frame
def currentType : Program 1 := leftOf framePayload
def currentCutoff : Program 1 := leftOf (rightOf framePayload)
def currentRaw : Program 1 := rightOf (rightOf framePayload)
def childCutoff : Program 1 := InternalAcceptance.branch (sameOf (leftOf currentRaw) (constant 1 1)) currentCutoff (succOf currentCutoff)

def expandedOne : Program 1 := liveOf
  (consOf (visitOf currentType childCutoff (firstOf currentRaw)) (consOf (finishOf currentRaw) rest)) results

def expandedTwo : Program 1 := liveOf
  (consOf (visitOf currentType currentCutoff (firstOf currentRaw))
    (consOf (visitOf currentType currentCutoff (secondOf currentRaw)) (consOf (finishOf currentRaw) rest))) results

def leafReturned (mode : Mode) : Program 1 := liveOf rest
  (consOf (.composition (leaf mode) ![currentType,currentCutoff,currentRaw]) results)

def returnedOne (mode : Mode) : Program 1 := liveOf rest
  (consOf (.composition (rebuild mode) ![framePayload,headOf results,constant 1 0]) (tailOf results))

def returnedTwo (mode : Mode) : Program 1 := liveOf rest
  (consOf (.composition (rebuild mode) ![framePayload,headOf (tailOf results),headOf results]) (tailOf (tailOf results)))

def transition (mode : Mode) : Program 1 :=
  InternalAcceptance.branch (sameOf status (constant 1 1)) (constant 1 0)
    (InternalAcceptance.branch work (.projection 0)
      (InternalAcceptance.branch (sameOf frameTag (constant 1 0))
        (InternalAcceptance.branch (sameOf frameTag (constant 1 1)) (constant 1 0)
          (InternalAcceptance.branch (sameOf (arityOf framePayload) (constant 1 1))
            (InternalAcceptance.branch (sameOf (arityOf framePayload) (constant 1 2)) (constant 1 0)
              (InternalAcceptance.branch results (constant 1 0)
                (InternalAcceptance.branch (tailOf results) (constant 1 0) (returnedTwo mode))))
            (InternalAcceptance.branch results (constant 1 0) (returnedOne mode))))
        (InternalAcceptance.branch (sameOf (arityOf currentRaw) (constant 1 1))
          (InternalAcceptance.branch (sameOf (arityOf currentRaw) (constant 1 2)) (leafReturned mode) expandedTwo)
          expandedOne)))

/-- Inputs [count, initial]. Each visit carries its own cutoff and erased type. -/
def iterate (mode : Mode) : Program 2 := .recursion (.projection (0 : Fin 1))
  (.composition (transition mode) (fun _ : Fin 1 => .projection (1 : Fin 3)))

def fuel : Program 3 := succOf (addOf (.projection 2) (.projection 2))
def initial : Program 3 := liveOf
  (consOf (visitOf (.projection 0) (.projection 1) (.projection 2)) (constant 3 0)) (constant 3 0)
def run (mode : Mode) : Program 3 := .composition (iterate mode) ![fuel,initial]
abbrev output := InternalApplicationResultStack.output
def fold (mode : Mode) : Program 3 := .composition output (fun _ : Fin 1 => run mode)

/-- Public payload interfaces. No packed outer type, context or Encodable Code
is accepted in the raw-code position. All three are explicit computational ASTs. -/
def shiftRaw : Program 2 := .composition (fold .shift) ![constant 2 0,.projection 0,.projection 1]
def eraseRaw : Program 3 := fold .erase
def variableRankRaw : Program 1 := .composition (fold .rank) ![constant 1 0,constant 1 0,.projection 0]

/-- Packed wrappers preserve the original outer type literally, at every raw
input. They do not canonicalize, type-check or change an Object's Gamma. -/
def shiftPackedRaw : Program 2 := pairOf (leftOf (.projection 1))
  (.composition shiftRaw ![.projection 0,rightOf (.projection 1)])
def erasePackedRaw : Program 3 := pairOf (leftOf (.projection 2))
  (.composition eraseRaw ![.projection 0,.projection 1,rightOf (.projection 2)])
def variableRankPackedRaw : Program 1 := .composition variableRankRaw (fun _ : Fin 1 => InternalUnpair.right)

/-- Literal ORIGINAL codeNumber constructors. Metadata are arbitrary raw
numbers here. There is no packed outer type and no well-typedness guard. -/
def variableConstructor : Program 1 := pairOf (constant 1 0) (.projection 0)
def lambdaConstructor : Program 2 := pairOf (constant 2 1) (pairOf (.projection 0) (.projection 1))
def applicationConstructor : Program 3 := pairOf (constant 3 2)
  (pairOf (.projection 0) (pairOf (.projection 1) (.projection 2)))
def bottomConstructor : Program 1 := pairOf (constant 1 3) (.projection 0)
def ordinaryConstructor : Program 2 := pairOf (constant 2 4) (pairOf (.projection 0) (.projection 1))
def numberedConstructor : Program 6 := pairOf (constant 6 5)
  (pairOf (.projection 0) (pairOf (.projection 1) (pairOf (.projection 2)
    (pairOf (.projection 3) (pairOf (.projection 4) (.projection 5))))))
def nilConstructor : Program 0 := pairOf (constant 0 6) (constant 0 0)
def consConstructor : Program 3 := pairOf (constant 3 7)
  (pairOf (.projection 0) (pairOf (.projection 1) (.projection 2)))

/-- Inputs [erased type, cutoff, variable index], exposing the literal leaf
case independently of traversal. Internal branch specifications are separate. -/
def variableAction (mode : Mode) : Program 3 := .composition (leaf mode)
  ![.projection 0,.projection 1,.composition variableConstructor (fun _ : Fin 1 => .projection 2)]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransport
