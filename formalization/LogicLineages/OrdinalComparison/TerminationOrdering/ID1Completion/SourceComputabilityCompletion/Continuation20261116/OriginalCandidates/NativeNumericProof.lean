module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidates.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidates.NativeNumericProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedMultisetNumeric NumberedMultisetNumericSupportProof
open InternalApplicationCertificateConstructorsEvaluationProof
open OriginalRawSyntaxTransportEvaluationSupportProof
open InternalRawListRecursionEvaluationProof

theorem stepValue (H : Program 1) (candidate rest gamma : Nat) :
    evaluate (filterStep H) (candidate ::ᵥ rest ::ᵥ gamma ::ᵥ nil) =
      if evaluate (OriginalTypedDecoder.packedCheck H) (ofFn ![candidate,gamma]) = 0 then rest
      else 1 + Nat.pair candidate rest := by
  rw [filterStep,InternalAcceptanceCalibrationProof.evalBranch,binaryCompositionEvaluation]
  change (if evaluate (OriginalTypedDecoder.packedCheck H) (ofFn ![candidate,gamma]) = 0 then rest else _) = _
  rw [consOfEvaluation]
  rfl

theorem filterFold (H : Program 1) (xs : List Nat) (gamma : Nat) :
    xs.foldr (fun candidate rest => evaluate (filterStep H) (candidate ::ᵥ rest ::ᵥ gamma ::ᵥ nil)) 0 =
      numbersNumber (xs.filter (fun candidate => decide (evaluate (OriginalTypedDecoder.packedCheck H) (ofFn ![candidate,gamma]) ≠ 0))) := by
  induction xs with
  | nil => rfl
  | cons candidate xs ih =>
    rw [List.foldr_cons,stepValue,ih]
    rw [List.filter_cons]
    by_cases h : evaluate (OriginalTypedDecoder.packedCheck H) (candidate ::ᵥ gamma ::ᵥ nil) = 0 <;>
      simp [h,numbersNumber]

theorem filterValue (H : Program 1) (xs : List Nat) (gamma : Nat) :
    evaluate (filterCandidates H) (ofFn ![numbersNumber xs,gamma]) =
      numbersNumber (xs.filter (fun candidate => decide (evaluate (OriginalTypedDecoder.packedCheck H) (ofFn ![candidate,gamma]) ≠ 0))) := by
  change evaluate (filterCandidates H) (numbersNumber xs ::ᵥ gamma ::ᵥ nil) = _
  rw [filterCandidates,actualRawListRecursionEvaluation,numbersRoundTrip]
  exact filterFold H xs gamma

theorem filterZero (H : Program 1) (gamma : Nat) :
    evaluate (filterCandidates H) (ofFn ![0,gamma]) = 0 := filterValue H [] gamma
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidates.NativeNumericProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidates.NativeNumericProof
