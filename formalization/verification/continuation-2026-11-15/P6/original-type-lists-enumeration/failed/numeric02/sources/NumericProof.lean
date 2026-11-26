module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsEnumeration.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesChildren.NativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalSourceHeads.RawProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsEnumeration.NumericProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedMultisetNumeric NumberedMultisetNumericSupportProof
open InternalRawListRecursionEvaluationProof InternalPairingEvaluationProof InternalListCodecEvaluationProof
open Continuation20261114

theorem rowStepValue (head tail left : Nat) :
    evaluate rowStep (head ::ᵥ tail ::ᵥ left ::ᵥ nil) = 1 + Nat.pair ((1 + Nat.pair left head)) tail := by
  change evaluate InternalListCodec.consCode (ofFn ![evaluate InternalListCodec.consCode
    (ofFn ![left,head]),tail]) = _
  rw [vectorTwo,consEvaluation]
  congr 1
  congr 1
  rw [vectorTwo,consEvaluation]
  rfl

theorem rowValue (right : List Nat) (left : Nat) :
    evaluate row (ofFn ![numbersNumber right,left]) =
      numbersNumber (right.map (fun b => (1 + Nat.pair left b))) := by
  have h := actualRawListRecursionEvaluation 1 (InternalAcceptance.constantZero 1) rowStep
    (left ::ᵥ nil) (numbersNumber right)
  change evaluate row (ofFn ![numbersNumber right,left]) = _ at h
  rw [h,numbersRoundTrip]
  change right.foldr (fun head rest => evaluate rowStep (head ::ᵥ rest ::ᵥ left ::ᵥ nil)) 0 = _
  clear h
  induction right with
  | nil => rfl
  | cons head tail ih => rw [List.foldr_cons,rowStepValue,ih,List.map_cons,numbersNumber]

theorem crossStepValue (head : Nat) (tail right : List Nat) :
    evaluate crossStep (head ::ᵥ numbersNumber tail ::ᵥ numbersNumber right ::ᵥ nil) =
      numbersNumber (right.map (fun b => (1 + Nat.pair head b)) ++ tail) := by
  change evaluate InternalApplicationValidityStackAppend.append
    (ofFn ![evaluate row (ofFn ![numbersNumber right,head]),numbersNumber tail]) = _
  rw [rowValue,OriginalSourceHeads.RawProof.appendValue]

theorem crossValue (left right : List Nat) :
    evaluate cross (ofFn ![numbersNumber left,numbersNumber right]) =
      numbersNumber (left.flatMap (fun a => right.map (fun b => (1 + Nat.pair a b)))) := by
  have h := actualRawListRecursionEvaluation 1 (InternalAcceptance.constantZero 1) crossStep
    (numbersNumber right ::ᵥ nil) (numbersNumber left)
  change evaluate cross (ofFn ![numbersNumber left,numbersNumber right]) = _ at h
  rw [h,numbersRoundTrip]
  change left.foldr (fun head rest => evaluate crossStep (head ::ᵥ rest ::ᵥ numbersNumber right ::ᵥ nil)) 0 = _
  clear h
  induction left with
  | nil => rfl
  | cons head tail ih => rw [List.foldr_cons,ih,crossStepValue,List.flatMap_cons]

def tuples (types : List Nat) : Nat → List Nat
  | 0 => [0]
  | count+1 => 0 :: types.flatMap (fun a => (tuples types count).map (fun b => 1 + Nat.pair a b))

theorem stepValue (count : Nat) (previous types : List Nat) :
    evaluate step (count ::ᵥ numbersNumber previous ::ᵥ numbersNumber types ::ᵥ nil) =
      numbersNumber (0 :: types.flatMap (fun a => previous.map (fun b => 1 + Nat.pair a b))) := by
  change evaluate InternalListCodec.consCode
    (ofFn ![0,evaluate cross (ofFn ![numbersNumber types,numbersNumber previous])]) = _
  rw [crossValue,vectorTwo,consEvaluation]
  rfl

theorem enumerationValue (types : List Nat) (count : Nat) :
    evaluate enumeration (ofFn ![count,numbersNumber types]) = numbersNumber (tuples types count) := by
  change Nat.rec (motive := fun _ => Nat) 1 (fun k previous => evaluate step (k ::ᵥ previous ::ᵥ numbersNumber types ::ᵥ nil)) count = _
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [Nat.rec_succ,ih,stepValue]
    rfl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsEnumeration.NumericProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsEnumeration.NumericProof
