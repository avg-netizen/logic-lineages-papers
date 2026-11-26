module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangeNativeTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportEvaluationSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPathCheckerEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangeNativeEvaluationProof
open OriginalNumericListSortExchangeNative OriginalNumericListSortExchange NumberedMultisetNumeric NumberedMultisetNumericSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open InternalApplicationCertificateConstructorsEvaluationProof OriginalRawSyntaxTransportEvaluationSupportProof
open InternalEqualityTestEvaluationProof (vectorTwo)
open InternalAcceptanceCalibrationProof
attribute [local irreducible] InternalPairing.pairing InternalUnpair.left InternalUnpair.right InternalListCodec.consCode

def inputs (m : Move) : List.Vector Nat 3 :=
 numbersNumber m.source ::ᵥ numbersNumber m.target ::ᵥ m.certificate ::ᵥ nil

theorem frontValue (m : Move) : evaluate front (inputs m) = numbersNumber m.front := by
 rw [front,leftOfEvaluation]
 change (Nat.unpair m.certificate).1 = _
 simp only [Move.certificate,Nat.unpair_pair]
theorem payloadValue (m : Move) : evaluate payload (inputs m) = Nat.pair m.first (Nat.pair m.second (numbersNumber m.tail)) := by
 rw [payload,rightOfEvaluation]
 change (Nat.unpair m.certificate).2 = _
 simp only [Move.certificate,Nat.unpair_pair]
theorem firstValue (m : Move) : evaluate first (inputs m) = m.first := by
 rw [first,leftOfEvaluation,payloadValue,Nat.unpair_pair]
theorem restValue (m : Move) : evaluate rest (inputs m) = Nat.pair m.second (numbersNumber m.tail) := by
 rw [rest,rightOfEvaluation,payloadValue,Nat.unpair_pair]
theorem secondValue (m : Move) : evaluate second (inputs m) = m.second := by
 rw [second,leftOfEvaluation,restValue,Nat.unpair_pair]
theorem tailValue (m : Move) : evaluate tail (inputs m) = numbersNumber m.tail := by
 rw [OriginalNumericListSortExchange.tail,rightOfEvaluation,restValue,Nat.unpair_pair]
theorem firstSecondValue (m : Move) : evaluate firstSecond (inputs m) = numbersNumber (m.first :: m.second :: m.tail) := by
 rw [firstSecond,consOfEvaluation,firstValue,afterSecond,consOfEvaluation,secondValue,tailValue]
 rfl
theorem secondFirstValue (m : Move) : evaluate secondFirst (inputs m) = numbersNumber (m.second :: m.first :: m.tail) := by
 rw [secondFirst,consOfEvaluation,secondValue,afterFirst,consOfEvaluation,firstValue,tailValue]
 rfl
theorem sourceEndpointValue (m : Move) : evaluate sourceEndpoint (inputs m) = numbersNumber m.source := by
 rw [sourceEndpoint,binaryCompositionEvaluation,vectorTwo,frontValue,firstSecondValue]
 exact OriginalContextInsertionCalibrationProof.appendNumbers _ _
theorem targetEndpointValue (m : Move) : evaluate targetEndpoint (inputs m) = numbersNumber m.target := by
 rw [targetEndpoint,binaryCompositionEvaluation,vectorTwo,frontValue,secondFirstValue]
 exact OriginalContextInsertionCalibrationProof.appendNumbers _ _
theorem acceptedMove (m : Move) : evaluate edge (inputs m) = 1 := by
 rw [edge,actualConjunctionEvaluation,sourceMatch,sameOfEvaluation,targetMatch,sameOfEvaluation,
   sourceEndpointValue,targetEndpointValue]
 change (if (if numbersNumber m.source = numbersNumber m.source then 1 else 0) = 1 ∧
   (if numbersNumber m.target = numbersNumber m.target then 1 else 0) = 1 then 1 else 0) = 1
 simp

open InternalPathCheckerEvaluationProof

theorem summaryAtCode (ms : List Move) (target : Nat) :
 evaluate (InternalPathChecker.summary edge) (pathCode ms ::ᵥ target ::ᵥ nil) =
 foldedSummary edge target (entries ms) := by
 rw [InternalPathChecker.summary,InternalRawListRecursionEvaluationProof.actualRawListRecursionEvaluation]
 rw [pathCode,numbersRoundTrip]
 rfl

theorem traceFinish {xs ys ms} (ht : Trace xs ys ms) :
 evaluate (InternalPathChecker.finish edge false)
   (numbersNumber xs ::ᵥ numbersNumber ys ::ᵥ foldedSummary edge (numbersNumber ys) (entries ms) ::ᵥ nil) = 1 := by
 induction ht with
 | nil xs => simp [entries,foldedSummaryNil,finishZeroEvaluation]
 | cons m ht ih =>
   change evaluate (InternalPathChecker.finish edge false)
     (numbersNumber m.source ::ᵥ _ ::ᵥ foldedSummary edge _ ((numbersNumber m.target,m.certificate) :: entries _) ::ᵥ nil) = 1
   rw [foldedSummaryCons,finishConsEvaluation,Nat.unpair_pair]
   have he := acceptedMove m
   change evaluate edge (numbersNumber m.source ::ᵥ numbersNumber m.target ::ᵥ m.certificate ::ᵥ nil) = 1 at he
   rw [he,ih]
   simp

theorem traceAccepted {xs ys ms} (ht : Trace xs ys ms) :
 evaluate (InternalPathChecker.checker edge false)
   (numbersNumber xs ::ᵥ numbersNumber ys ::ᵥ pathCode ms ::ᵥ nil) = 1 := by
 rw [checkerEvaluation,summaryAtCode]
 exact traceFinish ht
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangeNativeEvaluationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangeNativeEvaluationProof
