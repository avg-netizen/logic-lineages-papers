module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypedRequestsDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericTypedValidationDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformParameterLeavesDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoder
open Source Source.SourceMarkedSyntax NumberedAuxiliaryCoding NumberedAuxiliaryDecoding
open NumberedLeastCodeRepresentative NumberedNumericDecoding NumberedMultisetNumeric
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Only the unchanged local head metadata may be selected opaquely. Zero is
invalid; a valid head returns successor(pair(result type, ordered argument types)). -/
def headSignatureValue (n : Nat) (arity : Fin n → Nat) (raw : Nat) : Nat :=
  match decodeHeadNumber n raw with
  | none => 0
  | some head => 1 + Nat.pair (typeNumber (headResult (decodeHead head)))
      (typesNumber (headArguments arity (decodeHead head)))

def HeadSignatureCalibrated (n : Nat) (arity : Fin n → Nat) (H : Program 1) : Prop :=
  ∀ v : List.Vector Nat 1, evaluate H v = headSignatureValue n arity (v.get 0)

def ContextGuardCalibrated (n : Nat) (G : Program 1) : Prop :=
  ∀ v : List.Vector Nat 1, evaluate G v =
    (Encodable.decode (α := OrdinaryArithmeticQuotient.Context n) (v.get 0)).isSome.toNat

/-- Literal machine requests, not the unrelated Encodable instance of Request.
The context coordinate is the ORIGINAL Encodable Gamma throughout. -/
def termRequestValue (gamma typ raw : Nat) : Nat := Nat.pair 0 (Nat.pair gamma (Nat.pair typ raw))
def argumentsRequestValue (gamma types raw : Nat) : Nat := Nat.pair 1 (Nat.pair gamma (Nat.pair types raw))
def requestMode (request : Nat) : Nat := (Nat.unpair request).1
def requestGamma (request : Nat) : Nat := (Nat.unpair (Nat.unpair request).2).1
def requestType (request : Nat) : Nat := (Nat.unpair (Nat.unpair (Nat.unpair request).2).2).1
def requestRaw (request : Nat) : Nat := (Nat.unpair (Nat.unpair (Nat.unpair request).2).2).2

def encodeRequest {n : Nat} : NumberedTypedRequests.Request n → Nat
  | .term Gamma tau code => termRequestValue (Encodable.encode Gamma) (typeNumber tau) (codeNumber code)
  | .arguments Gamma types code => argumentsRequestValue (Encodable.encode Gamma) (typesNumber types) (codeNumber code)

def decodeRequest (n request : Nat) : Option (NumberedTypedRequests.Request n) := do
  let Gamma ← Encodable.decode (α := List Ty) (requestGamma request)
  let code ← decodeCode n (requestRaw request)
  if requestMode request = 0 then
    let tau ← decodeType (requestType request)
    pure (.term Gamma tau code)
  else if requestMode request = 1 then
    let types ← decodeTypes (requestType request)
    pure (.arguments Gamma types code)
  else none

/-- Direct total raw-list drop and original nonempty/equality variable test. -/
def dropValue (index gamma : Nat) : Nat :=
  Nat.rec gamma (fun _ rest => (Nat.unpair (rest - 1)).2) index

def variableValue (typ index gamma : Nat) : Nat :=
  let rest := dropValue index gamma
  if rest = 0 then 0 else if typ = (Nat.unpair (rest - 1)).1 then 1 else 0

/-- This is the raw numeric implementation of NumberedTypedRequests.expand.
All eight ORIGINAL constructors and their order are preserved. In particular
numbered heads impose no equality between their head result and requested type. -/
def expandValue (H : Nat → Nat) (request : Nat) : Option (List Nat) :=
  let gamma := requestGamma request
  let typ := requestType request
  let raw := requestRaw request
  let tag := (Nat.unpair raw).1
  let p := (Nat.unpair raw).2
  if requestMode request = 0 then
    if tag = 0 then
      if variableValue typ p gamma = 1 then some [] else none
    else if tag = 1 then
      if typ ≠ 0 ∧ (Nat.unpair (typ - 1)).1 = (Nat.unpair p).1 then
        some [termRequestValue (1 + Nat.pair (Nat.unpair p).1 gamma)
          (Nat.unpair (typ - 1)).2 (Nat.unpair p).2]
      else none
    else if tag = 2 then
      some [termRequestValue gamma (1 + Nat.pair (Nat.unpair p).1 typ)
        (Nat.unpair (Nat.unpair p).2).1,
        termRequestValue gamma (Nat.unpair p).1 (Nat.unpair (Nat.unpair p).2).2]
    else if tag = 3 then
      if p = typ then some [] else none
    else if tag = 4 then
      let signature := H (Nat.unpair p).1
      if signature ≠ 0 ∧ (Nat.unpair (signature - 1)).1 = typ then
        some [argumentsRequestValue gamma (Nat.unpair (signature - 1)).2 (Nat.unpair p).2]
      else none
    else if tag = 5 then
      let p1 := (Nat.unpair p).2
      let p2 := (Nat.unpair p1).2
      let p3 := (Nat.unpair p2).2
      let p4 := (Nat.unpair p3).2
      let signature := H (Nat.unpair p1).1
      if signature ≠ 0 ∧ (Nat.unpair p2).1 = typ then
        some [argumentsRequestValue gamma (Nat.unpair (signature - 1)).2 (Nat.unpair p3).1,
          argumentsRequestValue gamma (Nat.unpair p4).1 (Nat.unpair p4).2]
      else none
    else none
  else if requestMode request = 1 then
    if tag = 6 then
      if p = 0 ∧ typ = 0 then some [] else none
    else if tag = 7 then
      if typ ≠ 0 ∧ (Nat.unpair (typ - 1)).1 = (Nat.unpair p).1 then
        some [termRequestValue gamma (Nat.unpair p).1 (Nat.unpair (Nat.unpair p).2).1,
          argumentsRequestValue gamma (Nat.unpair (typ - 1)).2 (Nat.unpair (Nat.unpair p).2).2]
      else none
    else none
  else none

structure State where
  status : Nat
  work : List Nat

def failedState : State := ⟨0, []⟩
def encodeState (state : State) : Nat := Nat.pair state.status (numbersNumber state.work)

def stateStep (H : Nat → Nat) (state : State) : State :=
  if state.status = 1 then
    match state.work with
    | [] => state
    | request :: rest => match expandValue H request with
      | none => failedState
      | some children => ⟨1, children ++ rest⟩
  else failedState

/-- Non-one status, unknown request/constructor, failed guard: literal zero.
Zero and the live empty state are fixed points. -/
def transitionValue (H : Nat → Nat) (state : Nat) : Nat :=
  if (Nat.unpair state).1 = 1 then
    let work := (Nat.unpair state).2
    if work = 0 then state else
      let request := (Nat.unpair (work - 1)).1
      let rest := (Nat.unpair (work - 1)).2
      match expandValue H request with
      | none => 0
      | some children => Nat.pair 1 (children.foldr (fun child tail => 1 + Nat.pair child tail) rest)
  else 0

def requestWeight (request : Nat) : Nat := requestRaw request + 1
def workWeight (work : List Nat) : Nat := (work.map requestWeight).sum
def initialValue (request : Nat) : Nat := Nat.pair 1 (1 + Nat.pair request 0)
def iterateValue (H : Nat → Nat) (count initial : Nat) : Nat :=
  Nat.rec initial (fun _ state => transitionValue H state) count

def finishedValue (state : Nat) : Nat :=
  if (Nat.unpair state).1 = 1 ∧ (Nat.unpair state).2 = 0 then 1 else 0

def checkValue (H : Nat → Nat) (request : Nat) : Nat :=
  finishedValue (iterateValue H (requestRaw request + 1) (initialValue request))

/-- The actual original dependent decoder chain at ALL raw inputs. These are
specifications, not leaf programs used by the transparent implementation. -/
def termDecoderValue (n : Nat) (arity : Fin n → Nat) (typ raw gamma : Nat) : Nat :=
  match Encodable.decode (α := List Ty) gamma, decodeType typ, decodeCode n raw with
  | some Gamma, some tau, some code => (decodeTerm arity Gamma tau code).isSome.toNat
  | _, _, _ => 0

def argumentsDecoderValue (n : Nat) (arity : Fin n → Nat) (types raw gamma : Nat) : Nat :=
  match Encodable.decode (α := List Ty) gamma, decodeTypes types, decodeCode n raw with
  | some Gamma, some ts, some code => (decodeArguments arity Gamma ts code).isSome.toNat
  | _, _, _ => 0

def packedDecoderValue (n : Nat) (arity : Fin n → Nat) (value gamma : Nat) : Nat :=
  match Encodable.decode (α := List Ty) gamma with
  | none => 0
  | some Gamma => (decodePackedNumber n arity Gamma value).isSome.toNat

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoder
