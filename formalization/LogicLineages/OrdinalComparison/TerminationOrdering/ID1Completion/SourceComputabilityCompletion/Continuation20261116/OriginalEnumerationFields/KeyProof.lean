module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportSelectorProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.KeyProof
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportSelectorProof OriginalRawSyntaxTransportEvaluationSupportProof
open InternalApplicationCertificateConstructorsEvaluationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalAcceptanceCalibrationProof
open Continuation20261114
open NumberedAuxiliaryCoding NumberedLeastCodeRepresentative
open NumberedMultisetNumeric (numbersNumber)

def nextBound (raw bound : Nat) : Nat := if tagValue raw = 1 then bound+1 else bound
def keys (key : Nat) : List Nat :=
  let raw := (Nat.unpair key).1
  let bound := (Nat.unpair key).2
  if arityValue raw = 0 then [] else
  if arityValue raw = 2 then
    [Nat.pair (firstValue raw) (nextBound raw bound),Nat.pair (secondValue raw) bound]
  else [Nat.pair (firstValue raw) (nextBound raw bound)]

theorem rankValue (key param : Nat) :
    evaluate rank (List.Vector.ofFn ![key,param]) = (Nat.unpair key).1 := by
  simp only [rank,keyRaw,leftOfEvaluation]
  rfl

theorem dependencyValue (key param : Nat) :
    evaluate dependency (List.Vector.ofFn ![key,param]) = numbersNumber (keys key) := by
  simp only [dependency,firstKey,secondKey,childBound,keyRaw,keyBound,
    evalBranch,sameOfEvaluation,constantEvaluation,arityOfEvaluation,
    consOfEvaluation,pairOfEvaluation,firstOfEvaluation,secondOfEvaluation,
    leftOfEvaluation,rightOfEvaluation,succOfEvaluation]
  change (if arityValue (Nat.unpair key).1 = 0 then 0 else
    if (if arityValue (Nat.unpair key).1 = 2 then 1 else 0) = 0 then _ else _) = _
  unfold keys nextBound tagValue
  by_cases h0 : arityValue (Nat.unpair key).1 = 0 <;>
    by_cases h2 : arityValue (Nat.unpair key).1 = 2 <;>
    by_cases h1 : (Nat.unpair (Nat.unpair key).1).1 = 1 <;>
    simp [h0,h2,h1,numbersNumber,InternalApplicationStepPeelEvaluationSupportProof.projectionEvaluation]

theorem keysProject (key : Nat) :
    (keys key).map (fun child => (Nat.unpair child).1) =
      ArgumentEntriesFrontier.rawChildren (Nat.unpair key).1 := by
  by_cases h0 : arityValue (Nat.unpair key).1 = 0 <;>
    by_cases h2 : arityValue (Nat.unpair key).1 = 2 <;>
    simp [keys,ArgumentEntriesFrontier.rawChildren,h0,h2,Nat.unpair_pair]

theorem rankDecrease (key child : Nat) (hc : child ∈ keys key) :
    (Nat.unpair child).1 < (Nat.unpair key).1 := by
  apply ArgumentEntriesFrontier.Proof.rawDecrease
  rw [← keysProject key]
  exact List.mem_map.mpr ⟨child,hc,rfl⟩

/-- Source binder update and source child ordering, independent of the executable graph. -/
def sourceChildren {n : Nat} (bound : Nat) : Code (Fin n) → List (Code (Fin n) × Nat)
  | .lam _ child => [(child,bound+1)]
  | .ordinary _ child => [(child,bound)]
  | .app _ left right | .argumentsCons _ left right => [(left,bound),(right,bound)]
  | .numbered _ _ _ base _ extra => [(base,bound),(extra,bound)]
  | _ => []

theorem sourceImage (n : Nat) (c : Code (Fin n)) (bound : Nat) :
    keys (Nat.pair (codeNumber c) bound) =
      (sourceChildren bound c).map (fun x => Nat.pair (codeNumber x.1) x.2) := by
  cases c <;> simp [keys,nextBound,sourceChildren,codeNumber,arityValue,tagValue,
    firstValue,secondValue,payloadValue,Nat.unpair_pair]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.KeyProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.KeyProof
