module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldClosureTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultFoldCalibrationEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldClosureCalibrationProof
open InternalApplicationCertifiedResultFoldClosure InternalApplicationResultStack
open InternalApplicationResultStackEvaluationProof InternalApplicationResultStackStateProof
open InternalApplicationCertificateConstructorsEvaluationProof InternalAcceptanceCalibrationProof
open InternalApplicationValidityStackEvaluationProof (zeroEvaluation unaryEvaluation exactOneEvaluation)
open InternalApplicationResultFoldCalibrationEvaluationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem goodStateSingletonEvaluation (value : Nat) :
    evaluate goodState (List.Vector.ofFn ![encodeState (⟨1, [], [value]⟩ : State)]) = 1 := by
  simp only [goodState, evalBranch, exactOneEvaluation, statusEvaluation, workEvaluation,
    resultsEvaluation, tailOfEvaluation, zeroEvaluation]
  simp [encodeState, NumberedMultisetNumeric.numbersNumber, Nat.add_comm 1,
    InternalLessThan.constantOne, evaluate, InternalAcceptance.constantZero]

theorem actualOriginalResultFoldGoodRunCalibration :
    InternalApplicationCertifiedResultFoldClosureTargets.ActualOriginalResultFoldGoodRunCalibration := by
  intro guard leaf combine value
  rw [goodRun, unaryEvaluation, runSingletonEvaluation, goodStateSingletonEvaluation]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldClosureCalibrationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldClosureCalibrationProof
