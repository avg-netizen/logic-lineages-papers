module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportLeafRebuildProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportStateEvaluationProof
open OriginalRawSyntaxTransport InternalApplicationCertificateConstructors
open OriginalRawSyntaxTransportEvaluationSupportProof OriginalRawSyntaxTransportSelectorProof
open OriginalRawSyntaxTransportLeafRebuildProof
open InternalApplicationCertificateConstructorsEvaluationProof
open InternalAcceptanceCalibrationProof
open InternalApplicationResultStackEvaluationProof
  (headOfEvaluation tailOfEvaluation liveOfEvaluation)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

 theorem visitOfEvaluation {n : Nat} (d k raw : Program n) (v : List.Vector Nat n) :
    evaluate (visitOf d k raw) v = visitValue (evaluate d v) (evaluate k v) (evaluate raw v) := by
  simp only [visitOf, pairOfEvaluation, constantEvaluation, visitValue]

 theorem finishOfEvaluation {n : Nat} (raw : Program n) (v : List.Vector Nat n) :
    evaluate (finishOf raw) v = finishValue (evaluate raw v) := by
  simp only [finishOf, pairOfEvaluation, constantEvaluation, finishValue]

 theorem frameTagEvaluation (v : List.Vector Nat 1) :
    evaluate frameTag v = (Nat.unpair (evaluate frame v)).1 := by
  rw [frameTag, leftOfEvaluation]

 theorem framePayloadEvaluation (v : List.Vector Nat 1) :
    evaluate framePayload v = (Nat.unpair (evaluate frame v)).2 := by
  rw [framePayload, rightOfEvaluation]

 theorem currentTypeEvaluation (v : List.Vector Nat 1) :
    evaluate currentType v = (Nat.unpair (evaluate framePayload v)).1 := by
  rw [currentType, leftOfEvaluation]

 theorem currentCutoffEvaluation (v : List.Vector Nat 1) :
    evaluate currentCutoff v = (Nat.unpair (Nat.unpair (evaluate framePayload v)).2).1 := by
  rw [currentCutoff, leftOfEvaluation, rightOfEvaluation]

 theorem currentRawEvaluation (v : List.Vector Nat 1) :
    evaluate currentRaw v = (Nat.unpair (Nat.unpair (evaluate framePayload v)).2).2 := by
  rw [currentRaw, rightOfEvaluation, rightOfEvaluation]

 theorem childCutoffEvaluation (v : List.Vector Nat 1) :
    evaluate childCutoff v = if tagValue (evaluate currentRaw v) = 1
      then evaluate currentCutoff v + 1 else evaluate currentCutoff v := by
  simp only [childCutoff, evalBranch, sameOfEvaluation, leftOfEvaluation,
    constantEvaluation, succOfEvaluation, tagValue]
  split_ifs <;> simp_all

 theorem expandedOneEvaluation (v : List.Vector Nat 1) :
    evaluate expandedOne v = Nat.pair 1 (Nat.pair
      (1 + Nat.pair (visitValue (evaluate currentType v) (evaluate childCutoff v)
        (firstValue (evaluate currentRaw v)))
        (1 + Nat.pair (finishValue (evaluate currentRaw v)) (evaluate rest v)))
      (evaluate results v)) := by
  simp only [expandedOne, liveOfEvaluation, consOfEvaluation, visitOfEvaluation,
    finishOfEvaluation, firstOfEvaluation]

 theorem expandedTwoEvaluation (v : List.Vector Nat 1) :
    evaluate expandedTwo v = Nat.pair 1 (Nat.pair
      (1 + Nat.pair (visitValue (evaluate currentType v) (evaluate currentCutoff v)
        (firstValue (evaluate currentRaw v)))
        (1 + Nat.pair (visitValue (evaluate currentType v) (evaluate currentCutoff v)
          (secondValue (evaluate currentRaw v)))
          (1 + Nat.pair (finishValue (evaluate currentRaw v)) (evaluate rest v))))
      (evaluate results v)) := by
  simp only [expandedTwo, liveOfEvaluation, consOfEvaluation, visitOfEvaluation,
    finishOfEvaluation, firstOfEvaluation, secondOfEvaluation]

 theorem leafReturnedEvaluation (mode : Mode) (v : List.Vector Nat 1) :
    evaluate (leafReturned mode) v = Nat.pair 1 (Nat.pair (evaluate rest v)
      (1 + Nat.pair (leafValue mode (evaluate currentType v) (evaluate currentCutoff v)
        (evaluate currentRaw v)) (evaluate results v))) := by
  rw [leafReturned, liveOfEvaluation, consOfEvaluation, ternaryCompositionEvaluation, leafEvaluation]
  rfl

 theorem returnedOneEvaluation (mode : Mode) (v : List.Vector Nat 1) :
    evaluate (returnedOne mode) v = Nat.pair 1 (Nat.pair (evaluate rest v)
      (1 + Nat.pair (rebuildValue mode (evaluate framePayload v)
        (Nat.unpair (evaluate results v - 1)).1 0) (Nat.unpair (evaluate results v - 1)).2)) := by
  simp only [returnedOne, liveOfEvaluation, consOfEvaluation, ternaryCompositionEvaluation,
    rebuildEvaluation, List.Vector.get_ofFn, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, headOfEvaluation, tailOfEvaluation, constantEvaluation]
  rfl

 theorem returnedTwoEvaluation (mode : Mode) (v : List.Vector Nat 1) :
    evaluate (returnedTwo mode) v = Nat.pair 1 (Nat.pair (evaluate rest v)
      (1 + Nat.pair (rebuildValue mode (evaluate framePayload v)
        (Nat.unpair ((Nat.unpair (evaluate results v - 1)).2 - 1)).1
        (Nat.unpair (evaluate results v - 1)).1)
        (Nat.unpair ((Nat.unpair (evaluate results v - 1)).2 - 1)).2)) := by
  simp only [returnedTwo, liveOfEvaluation, consOfEvaluation, ternaryCompositionEvaluation,
    rebuildEvaluation, List.Vector.get_ofFn, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, headOfEvaluation, tailOfEvaluation]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportStateEvaluationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportStateEvaluationProof
