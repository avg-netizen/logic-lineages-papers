module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.TwoSol20261113.CalibratedPrimary.MembershipNativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionCalibrationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.ListNativeProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedMultisetNumeric NumberedMultisetNumericSupportProof
open OriginalRawSyntaxTransportEvaluationSupportProof
open InternalAcceptanceCalibrationProof
open Continuation20261115
open TwoSol20261113.CalibratedPrimary MembershipNativeProof

theorem bothValue {k : Nat} (p q : Program k) (v : List.Vector Nat k) :
    evaluate (both p q) v = if evaluate p v = 0 then 0 else evaluate q v := by
  rw [both,evalBranch,constantEvaluation]

theorem allStepValue (head rest allowed : Nat) :
    evaluate allStep (head ::ᵥ rest ::ᵥ allowed ::ᵥ nil) =
      if head ∈ (decodeNumbers allowed).getD [] then rest else 0 := by
  rw [allStep,bothValue]
  change (if evaluate Membership.contains (ofFn ![allowed,head]) = 0 then 0 else rest) = _
  rw [actualContainsNative]
  by_cases h : head ∈ (decodeNumbers allowed).getD [] <;> simp [h]

theorem allFold (xs : List Nat) (allowed : Nat) :
    xs.foldr (fun head rest => evaluate allStep (head ::ᵥ rest ::ᵥ allowed ::ᵥ nil)) 1 =
      (xs.all (fun head => decide (head ∈ (decodeNumbers allowed).getD []))).toNat := by
  induction xs with
  | nil => rfl
  | cons head tail ih =>
    rw [List.foldr_cons,ih,allStepValue,List.all_cons]
    by_cases h : head ∈ (decodeNumbers allowed).getD [] <;> simp [h]

theorem allTypesValue (raw allowed : Nat) :
    evaluate allTypes (ofFn ![raw,allowed]) =
      (((decodeNumbers raw).getD []).all (fun head => decide (head ∈ (decodeNumbers allowed).getD []))).toNat := by
  have h := InternalRawListRecursionEvaluationProof.actualRawListRecursionEvaluation
    1 (OriginalRawSyntaxTransport.constant 1 1) allStep (allowed ::ᵥ nil) raw
  change evaluate allTypes (ofFn ![raw,allowed]) = _ at h
  rw [h]
  change ((decodeNumbers raw).getD []).foldr
    (fun head rest => evaluate allStep (head ::ᵥ rest ::ᵥ allowed ::ᵥ nil)) 1 = _
  exact allFold _ allowed

theorem allTypesAccept (raw allowed : Nat) :
    evaluate allTypes (ofFn ![raw,allowed]) = 1 ↔
      ∀ x ∈ (decodeNumbers raw).getD [], x ∈ (decodeNumbers allowed).getD [] := by
  rw [allTypesValue]
  simp

theorem convertedHeadsValue (n raw : Nat) :
    evaluate (OriginalEncodedNumberedEnumerationBranch.convertedHeads n) (ofFn ![raw]) =
      numbersNumber (((decodeNumbers raw).getD []).map (fun h =>
        ((Encodable.decode (α := NumberedAuxiliaryCoding.HeadCode (Fin n)) h).map
          NumberedLeastCodeRepresentative.headNumber).getD 0)) := by
  have hm := InternalListMapEvaluationProof.actualRawListMapEvaluation 0
    (OriginalEncodedHeadConversion.convert n) nil raw
  change evaluate (OriginalEncodedNumberedEnumerationBranch.convertedHeads n) (ofFn ![raw]) = _ at hm
  rw [hm]
  congr 1
  apply List.map_congr_left
  intro h _
  exact OriginalEncodedHeadConversion.NativeProof.nativeConversion n h
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.ListNativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.ListNativeProof
