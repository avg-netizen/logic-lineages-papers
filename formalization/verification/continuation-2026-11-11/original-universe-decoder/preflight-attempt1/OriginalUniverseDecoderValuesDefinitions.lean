module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderValuesDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniverseEvaluationDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniverseNumericValidationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoder
open Source Source.SourceMarkedSyntax NumberedAuxiliaryCoding NumberedAuxiliaryDecoding
open NumberedFiniteUniverse NumberedNumericDecoding OriginalTypedDecoder
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Only a single ORIGINAL decoded head and ORIGINAL outer Context are inspected.
The original finite-table codec is retained, including malformed rejection. -/
def headWindowValue (n : Nat) (arity : Fin n → Nat) (head context : Nat) : Nat :=
  match decodeHeadNumber n head,
      Encodable.decode (α := OrdinaryArithmeticQuotient.Context n) context with
  | some h, some ctx => (decide (HeadInWindow arity ctx.1.1 ctx.1.2 (decodeHead h))).toNat
  | _, _ => 0

def HeadWindowCalibrated (n : Nat) (arity : Fin n → Nat) (W : Program 2) : Prop :=
  ∀ v : List.Vector Nat 2, evaluate W v = headWindowValue n arity (v.get 0) (v.get 1)

/-- The original type membership function at the unchanged outer Context. -/
def contextMemberValue (n typ context : Nat) : Nat :=
  match Encodable.decode (α := OrdinaryArithmeticQuotient.Context n) context with
  | some ctx => InternalStructuralEndpointGuard.membershipValue ctx.1.2 typ
  | none => 0

def ContextMemberCalibrated (n : Nat) (M : Program 2) : Prop :=
  ∀ v : List.Vector Nat 2, evaluate M v = contextMemberValue n (v.get 0) (v.get 1)

def programValue2 (P : Program 2) (first second : Nat) : Nat :=
  evaluate P (List.Vector.ofFn ![first,second])

/-- Literal local guard at [request,outerContext]. Every term checks its
requested type. Lambda also checks its domain; ordinary and numbered nodes
also check their ORIGINAL head. Arguments accept; unknown request modes reject.
Every test accepts exactly one, even for arbitrary M and W. -/
def guardValue (M W : Nat → Nat → Nat) (request context : Nat) : Nat :=
  if requestMode request = 0 then
    if M (requestType request) context = 1 then
      let tag := (Nat.unpair (requestRaw request)).1
      let payload := (Nat.unpair (requestRaw request)).2
      if tag = 1 then if M (Nat.unpair payload).1 context = 1 then 1 else 0
      else if tag = 4 then if W (Nat.unpair payload).1 context = 1 then 1 else 0
      else if tag = 5 then if W (Nat.unpair (Nat.unpair payload).2).1 context = 1 then 1 else 0
      else 1
    else 0
  else if requestMode request = 1 then 1 else 0

/-- Guarded wrapper around the unchanged typed state step. -/
def stateStep (H : Nat → Nat) (M W : Nat → Nat → Nat) (context : Nat)
    (state : OriginalTypedDecoder.State) : OriginalTypedDecoder.State :=
  if state.status = 1 then
    match state.work with
    | [] => state
    | request :: _ =>
      if guardValue M W request context = 1 then OriginalTypedDecoder.stateStep H state
      else failedState
  else failedState

/-- Non-live returns zero; live-empty is unchanged. A live nonempty state
calls the OLD transition exactly when the literal local guard returns one. -/
def transitionValue (H : Nat → Nat) (M W : Nat → Nat → Nat) (state context : Nat) : Nat :=
  if (Nat.unpair state).1 = 1 then
    if (Nat.unpair state).2 = 0 then state
    else if guardValue M W (Nat.unpair ((Nat.unpair state).2 - 1)).1 context = 1 then
      OriginalTypedDecoder.transitionValue H state
    else 0
  else 0

def iterateValue (H : Nat → Nat) (M W : Nat → Nat → Nat) (count initial context : Nat) : Nat :=
  Nat.rec initial (fun _ state => transitionValue H M W state context) count

def checkValue (H : Nat → Nat) (M W : Nat → Nat → Nat) (request context : Nat) : Nat :=
  finishedValue (iterateValue H M W (requestRaw request + 1) (initialValue request) context)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoder
