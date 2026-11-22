module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedSharedSyntaxTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedSyntaxNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedValidityNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoStepDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserTableEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedSharedSyntaxNumericProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (constantZero)
open InternalAcceptanceCalibrationProof (actualConjunctionEvaluation)
open NumberedWindowSyntaxAlgorithm (syntaxBits)
open NumberedWindowInternalSparsePathEnvelope (run)
open NumberedWindowInternalAuxExchangeMemoStepTargets (TermSyntaxCalibrated currentKey)
open NumberedWindowInternalAuxExchangeMemoStepDataProof (args unaryValue)
open NumberedWindowInternalCoverLambdaSyntaxRowTargets (TypeSyntaxCalibrated)
open NumberedWindowInternalCoverSharedSyntaxNumericProof (exact_CoverSharedSyntaxStep)
open NumberedWindowInternalCoverSharedRecursionTargets (sharedSyntaxUpdate)
open NumberedWindowInternalCoverSelectedValidityTargets (selectedValidity headerAny layout)
open NumberedWindowInternalCoverSelectedValidityNumericProof (exact_CoverSelectedValidityCalibration)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalSparseFieldParser (scratchRow)
open NumberedWindowInternalSparseFieldParserTableEvaluationProof (rowZero rowSucc lookupAt)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (compositeThree)
open NumberedWindowInternalCoverRefinedSharedSyntaxTargets

private theorem current (i old : Nat) : evaluate currentKey (args i old) = i+1 := by
  rw [currentKey,unaryValue] <;> rfl

private theorem acceptedLayout (V : Program 1) (cv : TermSyntaxCalibrated V) (n : Nat)
    (h : (syntaxBits n).1 = true) : run (headerAny layout) n = 1 := by
  have original := cv n
  have selected := exact_CoverSelectedValidityCalibration V cv n
  change evaluate V (n ::ᵥ nil) = (syntaxBits n).1.toNat at original
  change evaluate (selectedValidity V) (n ::ᵥ nil) = (syntaxBits n).1.toNat at selected
  change evaluate (headerAny layout) (n ::ᵥ nil) = 1
  rw [selectedValidity,actualConjunctionEvaluation,original,h] at selected
  by_cases actual : evaluate (headerAny layout) (n ::ᵥ nil) = 1
  · exact actual
  · have reject : ¬ ((Bool.toNat true : Nat) = 1 ∧ evaluate (headerAny layout) (n ::ᵥ nil) = 1) :=
      fun check => actual check.2
    rw [if_neg reject] at selected
    cases selected

theorem exact_CoverRefinedSharedSyntaxStep : ExactCoverRefinedSharedSyntaxStep := by
  intro V T cv ct i old earlier
  change evaluate (refinedUpdate V T) (args i old) = (syntaxBits (i+1)).1.toNat
  rw [refinedUpdate,actualConjunctionEvaluation,exact_CoverSharedSyntaxStep V T cv ct i old earlier,
    headerOnRow,unaryValue,current]
  cases h : (syntaxBits (i+1)).1
  · have reject : ¬ ((Bool.toNat false : Nat) = 1 ∧
        evaluate (headerAny layout) ((i+1) ::ᵥ nil) = 1) := fun check => by cases check.1
    rw [if_neg reject]
  · have pass := acceptedLayout V cv (i+1) h
    change evaluate (headerAny layout) ((i+1) ::ᵥ nil) = 1 at pass
    rw [if_pos ⟨rfl,pass⟩]

private theorem selectedRow (V T : Program 1) (cv : TermSyntaxCalibrated V) (ct : TypeSyntaxCalibrated T)
    (n : Nat) :
    evaluate (scratchRow (constantZero 2) (refinedUpdate V T)) (n ::ᵥ 0 ::ᵥ 0 ::ᵥ nil) =
      (syntaxBits n).1.toNat := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => rw [rowZero]; rfl
    | succ i =>
      rw [rowSucc]
      apply exact_CoverRefinedSharedSyntaxStep V T cv ct
      intro child small
      rw [lookupAt (constantZero 2) (refinedUpdate V T) (0 ::ᵥ 0 ::ᵥ nil)
        i child (Nat.le_of_lt_succ small)]
      exact ih child small

theorem exact_CoverRefinedSharedSyntax : ExactCoverRefinedSharedSyntax := by
  intro V T cv ct n
  unfold refinedSyntax run
  rw [selectedMeasure,compositeThree]
  exact selectedRow V T cv ct n

#print axioms exact_CoverRefinedSharedSyntaxStep
#print axioms exact_CoverRefinedSharedSyntax

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedSharedSyntaxNumericProof
