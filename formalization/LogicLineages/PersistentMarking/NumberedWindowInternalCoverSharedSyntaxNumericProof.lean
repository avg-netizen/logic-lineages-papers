module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedRecursionTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxSyntaxNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaSyntaxRowNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserTableEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedSyntaxNumericProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (constantZero)
open InternalAcceptanceCalibrationProof (evalBranch)
open NumberedWindowSyntaxAlgorithm (syntaxBits)
open NumberedWindowInternalSparsePathEnvelope (run)
open NumberedWindowInternalAuxExchangeMemoStepTargets (TermSyntaxCalibrated)
open NumberedWindowInternalCoverLambdaSyntaxRowTargets (TypeSyntaxCalibrated)
open NumberedWindowInternalCoverLambdaSyntaxRowNumericProof (exact_CoverLambdaSyntaxStepCalibration)
open NumberedWindowInternalCoverAuxSyntaxNumericProof (exact_CoverAuxSyntaxStepCalibration)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalSparseFieldParser (scratchRow)
open NumberedWindowInternalSparseFieldParserTableEvaluationProof (rowZero rowSucc lookupAt)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (compositeThree)
open NumberedWindowInternalCoverSharedRecursionTargets

theorem exact_CoverSharedSyntaxStep : ExactCoverSharedSyntaxStep := by
  intro V T cv ct i old previous
  rw [sharedSyntaxUpdate,sharedUpdate,evalBranch]
  split
  · exact exact_CoverAuxSyntaxStepCalibration V T cv ct i old previous
  · exact exact_CoverLambdaSyntaxStepCalibration V T cv ct i old previous

private theorem selectedRow (V T : Program 1) (cv : TermSyntaxCalibrated V) (ct : TypeSyntaxCalibrated T)
    (n : Nat) :
    evaluate (scratchRow (constantZero 2) (sharedSyntaxUpdate V T)) (n ::ᵥ 0 ::ᵥ 0 ::ᵥ nil) =
      (syntaxBits n).1.toNat := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => rw [rowZero]; rfl
    | succ i =>
      rw [rowSucc]
      apply exact_CoverSharedSyntaxStep V T cv ct
      intro child small
      rw [lookupAt (constantZero 2) (sharedSyntaxUpdate V T) (0 ::ᵥ 0 ::ᵥ nil)
        i child (Nat.le_of_lt_succ small)]
      exact ih child small

theorem exact_CoverSharedSyntax : ExactCoverSharedSyntax := by
  intro V T cv ct n
  unfold sharedSyntax run
  rw [selectedMeasure,compositeThree]
  exact selectedRow V T cv ct n

#print axioms exact_CoverSharedSyntaxStep
#print axioms exact_CoverSharedSyntax

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedSyntaxNumericProof
