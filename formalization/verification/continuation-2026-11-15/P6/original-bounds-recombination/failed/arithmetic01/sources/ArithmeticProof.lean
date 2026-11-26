module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalBoundsRecombination.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalBoundsRecombination.ArithmeticProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open InternalAcceptanceCalibrationProof OriginalRawSyntaxTransportEvaluationSupportProof
open InternalApplicationCertificateConstructorsEvaluationProof
open NumberedSyntaxBoundsPrimrecSupportProof
open NumberedMultisetNumeric NumberedMultisetNumericSupportProof

theorem maximumValue (a b : Nat) : evaluate maximum (a ::ᵥ b ::ᵥ nil) = max a b := by
  rw [maximum,evalBranch,InternalLessThanEvaluationProof.exactLessThanEvaluation]
  change (if (if a < b then 1 else 0) = 0 then a else b) = max a b
  by_cases h : a < b
  · simp only [h,ite_true,Nat.one_ne_zero,ite_false,max_eq_right (Nat.le_of_lt h)]
  · simp only [h,ite_false,ite_true,max_eq_left (Nat.le_of_not_gt h)]

theorem mergeValue (a b : Nat) : evaluate merge (a ::ᵥ b ::ᵥ nil) =
    Nat.pair ((Nat.unpair a).1 + (Nat.unpair b).1) (max (Nat.unpair a).2 (Nat.unpair b).2) := by
  simp only [merge,pairOfEvaluation,addOfEvaluation,leftOfEvaluation,rightOfEvaluation,
    projectionEvaluation,binaryCompositionEvaluation]
  rw [InternalEqualityTestEvaluationProof.vectorTwo,maximumValue]
  rfl

theorem foldValue (xs : List Nat) :
    xs.foldr (fun head acc => evaluate merge (head ::ᵥ acc ::ᵥ nil)) 0 =
      Encodable.encode (collectBounds (xs.map Nat.unpair)) := by
  induction xs with
  | nil => rfl
  | cons head tail ih =>
    rw [List.foldr_cons,ih,mergeValue]
    simp only [collectBounds,List.map_cons,List.foldr_cons,mergeBounds,Encodable.encode_prod_val,Nat.unpair_pair]
    rfl

theorem collectValue (raw : Nat) : evaluate collect (raw ::ᵥ nil) =
    Encodable.encode (collectBounds (((decodeNumbers raw).getD []).map Nat.unpair)) := by
  rw [collect,InternalRawListRecursionEvaluationProof.actualRawListRecursionEvaluation]
  change ((decodeNumbers raw).getD []).foldr (fun head acc => evaluate merge (head ::ᵥ acc ::ᵥ nil)) 0 = _
  exact foldValue _
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalBoundsRecombination.ArithmeticProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalBoundsRecombination.ArithmeticProof
