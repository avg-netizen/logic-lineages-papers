module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.NumericDependencyCross.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesChildren.NativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalSourceHeads.RawProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.NumericDependencyCross.NativeProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedMultisetNumeric NumberedMultisetNumericSupportProof
open InternalRawListRecursionEvaluationProof InternalPairingEvaluationProof InternalListCodecEvaluationProof
open Continuation20261114

theorem rowStepValue (head tail left : Nat) :
    evaluate rowStep (head ::ᵥ tail ::ᵥ left ::ᵥ nil) = 1 + Nat.pair (Nat.pair left head) tail := by
  change evaluate InternalListCodec.consCode (ofFn ![evaluate InternalPairing.pairing
    (ofFn ![left,head]),tail]) = _
  rw [vectorTwo,consEvaluation]
  congr 1
  congr 1
  rw [vectorTwo,exactPairingEvaluation]

theorem rowValue (right : List Nat) (left : Nat) :
    evaluate row (ofFn ![numbersNumber right,left]) =
      numbersNumber (right.map (fun b => Nat.pair left b)) := by
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
      numbersNumber (right.map (fun b => Nat.pair head b) ++ tail) := by
  change evaluate InternalApplicationValidityStackAppend.append
    (ofFn ![evaluate row (ofFn ![numbersNumber right,head]),numbersNumber tail]) = _
  rw [rowValue,OriginalSourceHeads.RawProof.appendValue]

theorem crossValue (left right : List Nat) :
    evaluate cross (ofFn ![numbersNumber left,numbersNumber right]) =
      numbersNumber (left.flatMap (fun a => right.map (fun b => Nat.pair a b))) := by
  have h := actualRawListRecursionEvaluation 1 (InternalAcceptance.constantZero 1) crossStep
    (numbersNumber right ::ᵥ nil) (numbersNumber left)
  change evaluate cross (ofFn ![numbersNumber left,numbersNumber right]) = _ at h
  rw [h,numbersRoundTrip]
  change left.foldr (fun head rest => evaluate crossStep (head ::ᵥ rest ::ᵥ numbersNumber right ::ᵥ nil)) 0 = _
  clear h
  induction left with
  | nil => rfl
  | cons head tail ih => rw [List.foldr_cons,ih,crossStepValue,List.flatMap_cons]

theorem dependencyValue (n : Nat) (source target : NumberedAuxiliaryCoding.Code (Fin n)) :
    evaluate rawDependencies (ofFn ![NumberedLeastCodeRepresentative.codeNumber source,
      NumberedLeastCodeRepresentative.codeNumber target]) =
      numbersNumber ((NumberedExchangeCodeFieldsProof.dependencies (source,target)).map
        (fun child => Nat.pair (NumberedLeastCodeRepresentative.codeNumber child.1)
          (NumberedLeastCodeRepresentative.codeNumber child.2))) := by
  change evaluate cross (ofFn ![
    evaluate ArgumentEntriesChildren.children (ofFn ![NumberedLeastCodeRepresentative.codeNumber source]),
    evaluate ArgumentEntriesChildren.children (ofFn ![NumberedLeastCodeRepresentative.codeNumber target])]) = _
  rw [ArgumentEntriesChildren.NativeProof.nativeChildren,ArgumentEntriesChildren.NativeProof.nativeChildren,crossValue]
  simp only [NumberedExchangeCodeFieldsProof.dependencies,NumberedCodeEnumerationPrimrecSupportProof.cross,
    List.map_flatMap,List.flatMap_map,List.map_map]

theorem nativeCorrespondence : Targets.NativeCorrespondence := ⟨crossValue,dependencyValue⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.NumericDependencyCross.NativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.NumericDependencyCross.NativeProof
