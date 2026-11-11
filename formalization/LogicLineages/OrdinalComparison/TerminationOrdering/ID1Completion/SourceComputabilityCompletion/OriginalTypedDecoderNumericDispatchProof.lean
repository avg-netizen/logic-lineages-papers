module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderNumericDispatchProof
open OriginalTypedDecoder

/-- A local presentation of the frozen transition's Option elimination. -/
def expansionResult (rest : Nat) : Option (List Nat) → Nat
  | none => 0
  | some children => Nat.pair 1 (children.foldr (fun child tail => 1 + Nat.pair child tail) rest)

 theorem expansionResultNone (rest : Nat) : expansionResult rest none = 0 := rfl
 theorem expansionResultSome (rest : Nat) (children : List Nat) :
    expansionResult rest (some children) =
      Nat.pair 1 (children.foldr (fun child tail => 1 + Nat.pair child tail) rest) := rfl

 theorem expansionResultIf (rest : Nat) (p : Prop) [Decidable p]
    (yes no : Option (List Nat)) :
    expansionResult rest (if p then yes else no) =
      if p then expansionResult rest yes else expansionResult rest no := by
  by_cases h : p <;> simp only [h, if_true, if_false]

/-- These arithmetic presentations are proved equal to the frozen expandValue
below; they are not selected leaves or replacements for the original decoder. -/
def termResult (H : Nat → Nat) (gamma typ raw rest : Nat) : Nat :=
  let tag := (Nat.unpair raw).1
  let p := (Nat.unpair raw).2
  if tag = 0 then
    if variableValue typ p gamma = 1 then Nat.pair 1 rest else 0
  else if tag = 1 then
    if typ ≠ 0 ∧ (Nat.unpair (typ - 1)).1 = (Nat.unpair p).1 then
      Nat.pair 1 (1 + Nat.pair (termRequestValue (1 + Nat.pair (Nat.unpair p).1 gamma)
        (Nat.unpair (typ - 1)).2 (Nat.unpair p).2) rest)
    else 0
  else if tag = 2 then
    Nat.pair 1 (1 + Nat.pair (termRequestValue gamma (1 + Nat.pair (Nat.unpair p).1 typ)
      (Nat.unpair (Nat.unpair p).2).1)
      (1 + Nat.pair (termRequestValue gamma (Nat.unpair p).1 (Nat.unpair (Nat.unpair p).2).2) rest))
  else if tag = 3 then
    if p = typ then Nat.pair 1 rest else 0
  else if tag = 4 then
    let signature := H (Nat.unpair p).1
    if signature ≠ 0 ∧ (Nat.unpair (signature - 1)).1 = typ then
      Nat.pair 1 (1 + Nat.pair (argumentsRequestValue gamma (Nat.unpair (signature - 1)).2
        (Nat.unpair p).2) rest)
    else 0
  else if tag = 5 then
    let p1 := (Nat.unpair p).2
    let p2 := (Nat.unpair p1).2
    let p3 := (Nat.unpair p2).2
    let p4 := (Nat.unpair p3).2
    let signature := H (Nat.unpair p1).1
    if signature ≠ 0 ∧ (Nat.unpair p2).1 = typ then
      Nat.pair 1 (1 + Nat.pair (argumentsRequestValue gamma (Nat.unpair (signature - 1)).2
        (Nat.unpair p3).1)
        (1 + Nat.pair (argumentsRequestValue gamma (Nat.unpair p4).1 (Nat.unpair p4).2) rest))
    else 0
  else 0

def argumentsResult (gamma typ raw rest : Nat) : Nat :=
  let tag := (Nat.unpair raw).1
  let p := (Nat.unpair raw).2
  if tag = 6 then
    if p = 0 ∧ typ = 0 then Nat.pair 1 rest else 0
  else if tag = 7 then
    if typ ≠ 0 ∧ (Nat.unpair (typ - 1)).1 = (Nat.unpair p).1 then
      Nat.pair 1 (1 + Nat.pair (termRequestValue gamma (Nat.unpair p).1 (Nat.unpair (Nat.unpair p).2).1)
        (1 + Nat.pair (argumentsRequestValue gamma (Nat.unpair (typ - 1)).2
          (Nat.unpair (Nat.unpair p).2).2) rest))
    else 0
  else 0

 theorem expansionResultEvaluation (H : Nat → Nat) (request rest : Nat) :
    expansionResult rest (expandValue H request) =
      if requestMode request = 0 then
        termResult H (requestGamma request) (requestType request) (requestRaw request) rest
      else if requestMode request = 1 then
        argumentsResult (requestGamma request) (requestType request) (requestRaw request) rest
      else 0 := by
  simp only [expandValue, expansionResultIf, termResult, argumentsResult,
    expansionResultNone, expansionResultSome, List.foldr_cons, List.foldr_nil]

 theorem transitionValueEquation (H : Nat → Nat) (state : Nat) :
    transitionValue H state =
      if (Nat.unpair state).1 = 1 then
        if (Nat.unpair state).2 = 0 then state
        else expansionResult (Nat.unpair ((Nat.unpair state).2 - 1)).2
          (expandValue H (Nat.unpair ((Nat.unpair state).2 - 1)).1)
      else 0 := rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderNumericDispatchProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderNumericDispatchProof
