module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultFoldCalibrationCompletionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultFoldCalibrationEvaluationProof
open InternalApplicationResultStack InternalApplicationResultFoldCalibration
open InternalApplicationResultFoldCalibrationExecutionProof InternalApplicationResultFoldCalibrationCompletionProof
open InternalApplicationResultStackEvaluationProof InternalApplicationResultStackStateProof
open InternalApplicationCertificateConstructorsEvaluationProof InternalAcceptanceCalibrationProof
open InternalApplicationValidityStackEvaluationProof (zeroEvaluation unaryEvaluation exactOneEvaluation)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem initialEvaluation (value : Nat) :
    evaluate initial (List.Vector.ofFn ![value]) =
      encodeState (⟨1, [visitValue value], []⟩ : State) := by
  rw [initial, liveOfEvaluation, consOfEvaluation, visitOfEvaluation, zeroEvaluation]
  rfl

theorem runEvaluation (guard leaf : Program 1) (combine : Program 4) (value : Nat) :
    evaluate (run guard leaf combine) (List.Vector.ofFn ![value]) =
      encodeState (stateIterate
        (fun x => evaluate guard (List.Vector.ofFn ![x]))
        (fun x => evaluate leaf (List.Vector.ofFn ![x]))
        (fun d e f a => evaluate combine (List.Vector.ofFn ![d,e,f,a]))
        (fuelValue value) (⟨1, [visitValue value], []⟩ : State)) := by
  change evaluate (iterate guard leaf combine)
    (List.Vector.ofFn fun i : Fin 2 =>
      evaluate ((![fuel, initial] : Fin 2 → Program 1) i) (List.Vector.ofFn ![value])) = _
  have hv : (List.Vector.ofFn fun i : Fin 2 =>
      evaluate ((![fuel, initial] : Fin 2 → Program 1) i) (List.Vector.ofFn ![value])) =
      List.Vector.ofFn ![fuelValue value, encodeState (⟨1, [visitValue value], []⟩ : State)] := by
    apply List.Vector.ext
    intro i
    simp only [List.Vector.get_ofFn]
    refine Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j)) i
    · exact fuelEvaluation value
    · exact initialEvaluation value
  rw [hv, actualOriginalEncodedResultStackIteration]

theorem runSingletonEvaluation (guard leaf : Program 1) (combine : Program 4) (value : Nat) :
    evaluate (run guard leaf combine) (List.Vector.ofFn ![value]) =
      encodeState (⟨1, [], [semanticFold
        (fun x => evaluate guard (List.Vector.ofFn ![x]))
        (fun x => evaluate leaf (List.Vector.ofFn ![x]))
        (fun d e f a => evaluate combine (List.Vector.ofFn ![d,e,f,a])) value]⟩ : State) := by
  rw [runEvaluation, actualOriginalCompletedResultFold
    (fun x => evaluate guard (List.Vector.ofFn ![x]))
    (fun x => evaluate leaf (List.Vector.ofFn ![x]))
    (fun d e f a => evaluate combine (List.Vector.ofFn ![d,e,f,a]))
    value [] (fuelValue value) (Nat.le_refl _)]

theorem outputSingletonEvaluation (value : Nat) :
    evaluate output (List.Vector.ofFn ![encodeState (⟨1, [], [value]⟩ : State)]) = value := by
  simp only [output, evalBranch, exactOneEvaluation, statusEvaluation, workEvaluation,
    resultsEvaluation, tailOfEvaluation, headOfEvaluation, zeroEvaluation]
  simp [encodeState, NumberedMultisetNumeric.numbersNumber, Nat.add_comm 1]

theorem actualOriginalBoundedResultFoldCalibration :
    InternalApplicationResultFoldCalibrationTargets.ActualOriginalBoundedResultFoldCalibration := by
  intro guard leaf combine value
  dsimp only
  constructor
  · exact runSingletonEvaluation guard leaf combine value
  · rw [fold, unaryEvaluation, runSingletonEvaluation, outputSingletonEvaluation]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultFoldCalibrationEvaluationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultFoldCalibrationEvaluationProof
