module
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxSyntaxTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalFactoredCoverTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxSyntaxNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedAuxSyntaxRetargetProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptanceCalibrationProof (evalBranch)
open NumberedWindowInternalSparsePathEnvelope (run)
open NumberedWindowInternalCoverLambdaSyntaxRowTargets (TypeSyntaxCalibrated)
open NumberedWindowInternalCoverAuxSyntaxTargets (auxSyntax)
open NumberedWindowInternalCoverAuxSyntaxNumericProof (exact_CoverAuxSyntaxCalibration)
open NumberedWindowInternalFactoredCoverTargets (factoredCover rawCall)
open NumberedWindowInternalSparseCoverScratchTargets (ActualSelectedCoverOutput)
open NumberedWindowInternalSparseTypedRawTargets (ActualRawSyntax)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (vectorOne)

theorem exact_OriginalUnrestrictedAuxSyntaxCalibration (V TV : Program 1)
    (syntaxFit : ActualRawSyntax V) (typeFit : TypeSyntaxCalibrated TV) :
    ActualRawSyntax (auxSyntax V TV) :=
  exact_CoverAuxSyntaxCalibration V TV syntaxFit typeFit

private theorem rawValue (V : Program 1) (tape : List.Vector Nat 3) :
    evaluate (rawCall V) tape = run V (tape.get 2) := by
  change evaluate V (List.Vector.ofFn fun _ : Fin 1 => tape.get 2) = _
  rw [vectorOne] <;> rfl

/-- Compare the actual factored cover branches on their original tape. No
congruence of object-calculus derivations follows from this numeric fit. -/
theorem exact_OriginalUnrestrictedAuxCoverValue (V TV M : Program 1) (G : Program 3)
    (syntaxFit : ActualRawSyntax V) (typeFit : TypeSyntaxCalibrated TV)
    (H K : List Nat) (n : Nat) :
    let tape := Encodable.encode H ::ᵥ Encodable.encode K ::ᵥ n ::ᵥ nil
    evaluate (factoredCover (auxSyntax V TV) M G) tape =
      evaluate (factoredCover V M G) tape := by
  let tape := Encodable.encode H ::ᵥ Encodable.encode K ::ᵥ n ::ᵥ nil
  have same : run (auxSyntax V TV) (tape.get 2) = run V (tape.get 2) :=
    (exact_OriginalUnrestrictedAuxSyntaxCalibration V TV syntaxFit typeFit
      (tape.get 2)).trans (syntaxFit (tape.get 2)).symm
  change evaluate (factoredCover (auxSyntax V TV) M G) tape =
    evaluate (factoredCover V M G) tape
  simp only [factoredCover,evalBranch,rawValue,same]

theorem exact_OriginalUnrestrictedAuxCoverFit (V TV M : Program 1) (G : Program 3)
    (syntaxFit : ActualRawSyntax V) (typeFit : TypeSyntaxCalibrated TV)
    (coverFit : ActualSelectedCoverOutput (factoredCover V M G)) :
    ActualSelectedCoverOutput (factoredCover (auxSyntax V TV) M G) := by
  intro H K n
  exact (exact_OriginalUnrestrictedAuxCoverValue V TV M G syntaxFit typeFit H K n).trans (coverFit H K n)

#print axioms exact_OriginalUnrestrictedAuxSyntaxCalibration
#print axioms exact_OriginalUnrestrictedAuxCoverValue
#print axioms exact_OriginalUnrestrictedAuxCoverFit
end LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedAuxSyntaxRetargetProof
