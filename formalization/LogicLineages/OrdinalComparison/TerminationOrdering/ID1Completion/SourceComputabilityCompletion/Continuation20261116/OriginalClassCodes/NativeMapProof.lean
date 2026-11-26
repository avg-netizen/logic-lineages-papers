module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListMapEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadEncodingBridge.NativeStatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsEnumeration.CodecProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.NativeMapProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedMultisetNumeric NumberedMultisetNumericSupportProof
open NumberedLeastCodeRepresentative NumberedAuxiliaryCoding
open InternalApplicationCertificateConstructorsEvaluationProof
open OriginalRawSyntaxTransportEvaluationSupportProof
open InternalRawListRecursionEvaluationProof InternalListMapEvaluationProof
open Continuation20261114 Continuation20261115

theorem encodedHeads (n : Nat) (hs : List (HeadCode (Fin n))) :
    evaluate (InternalListMap.map OriginalHeadEncodingBridge.encodeHead)
      (ofFn ![numbersNumber (hs.map headNumber)]) = Encodable.encode hs := by
  rw [InternalEqualityTestEvaluationProof.vectorOne]
  change evaluate (InternalListMap.map OriginalHeadEncodingBridge.encodeHead)
    (numbersNumber (hs.map headNumber) ::ᵥ nil) = _
  rw [actualRawListMapEvaluation,numbersRoundTrip]
  simp only [Option.getD_some,List.map_map,OriginalTypeListsEnumeration.CodecProof.listEncoding]
  congr 1
  apply List.map_congr_left
  intro h _
  exact OriginalHeadEncodingBridge.NativeProof.nativeHeadEncoding n h

theorem pairStepValue (raw tail root : Nat) :
    evaluate pairStep (raw ::ᵥ tail ::ᵥ root ::ᵥ nil) = 1 + Nat.pair (Nat.pair root raw) tail := by
  simp only [pairStep,consOfEvaluation,pairOfEvaluation]
  rfl

theorem pairRootsFold (xs : List Nat) (root : Nat) :
    xs.foldr (fun raw tail => evaluate pairStep (raw ::ᵥ tail ::ᵥ root ::ᵥ nil)) 0 =
      numbersNumber (xs.map (fun raw => Nat.pair root raw)) := by
  induction xs with
  | nil => rfl
  | cons raw xs ih =>
    rw [List.foldr_cons,pairStepValue,ih]
    rfl

theorem pairRootsValue (xs : List Nat) (root : Nat) :
    evaluate pairRoots (ofFn ![numbersNumber xs,root]) =
      numbersNumber (xs.map (fun raw => Nat.pair root raw)) := by
  change evaluate pairRoots (numbersNumber xs ::ᵥ root ::ᵥ nil) = _
  rw [pairRoots,actualRawListRecursionEvaluation,numbersRoundTrip]
  exact pairRootsFold xs root

theorem pairRootsOriginal (n : Nat) (tau : Source.Ty) (xs : List (Code (Fin n))) :
    evaluate pairRoots (ofFn ![Encodable.encode xs,Encodable.encode tau]) =
      TwoSol20261113.CalibratedPrimary.Membership.entriesCode (xs.map (fun raw => (tau,raw))) := by
  rw [OriginalTypeListsEnumeration.CodecProof.listEncoding,pairRootsValue]
  simp only [TwoSol20261113.CalibratedPrimary.Membership.entriesCode,List.map_map]
  rfl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.NativeMapProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.NativeMapProof
