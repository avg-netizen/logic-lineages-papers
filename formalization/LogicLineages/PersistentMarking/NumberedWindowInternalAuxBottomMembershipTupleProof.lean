module
public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxBottomMembershipTupleTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementNumericChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxBottomRefinementNumericChecks
import LogicLineages.PersistentMarking.NumberedWindowFormulaCalibrationChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeReinstallChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeAlignmentChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAuxBottomMembershipTupleProof
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalAccessibilityRules
open ID1Completion.InternalAccessibilityRulesProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalProbeTargets (OTerm)
open NumberedWindowGuardedGraphTargets (InputGuards)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalAtomicRefinement (refined)
open NumberedWindowInternalAtomicRefinementNumericChecks (exact_OriginalRefinedPresentationEvaluation)
open NumberedWindowInternalAuxBottomRefinementNumericChecks (exact_OriginalAuxBottomRefinement)
open NumberedWindowFormulaCalibrationTargets (Evaluates)
open NumberedWindowFormulaCalibrationChecks (exact_InterpretsEvaluatingPrograms)
open NumberedWindowPresentationCheckers (checks)
open NumberedWindowInternalAtomicRefinementReinstallTargets (TupleAt)
open NumberedWindowInternalAtomicApplicationShapeReinstallTargets (BaseAt)
open NumberedWindowInternalAtomicApplicationShapeReinstallChecks (exact_ReinstallShapeRefinedApplication)
open NumberedWindowInternalFreshProbeAlignmentChecks (exact_ConcreteParsedFreshCarrierTuple)
open NumberedWindowInternalAuxBottomMembership (augmented)
open NumberedWindowInternalAuxBottomMembershipTupleTargets

theorem presentation : ExactAugmentedPresentation := by
  intro xs s i j r d old
  let R := augmented i r
  let S := data i j R d
  have bare := exact_OriginalRefinedPresentationEvaluation xs s i j r d old
  have exactEval : Evaluates (checks xs s) i j R d :=
    ⟨bare.1,bare.2.1,
      exact_OriginalAuxBottomRefinement xs s i (refined i r) bare.1 bare.2.2.1,
      bare.2.2.2⟩
  exact ⟨exactEval,exact_InterpretsEvaluatingPrograms (checks xs s) i j R d exactEval,
    ⟨actualOriginalMembershipEquation S,actualOriginalCarrierExtraction S,
      actualOriginalSuccessorClosure S,actualOriginalCertifiedSuccessorClosure S,
      actualOriginalAccessibilityIntroduction S⟩⟩

/-- The source carrier formula itself is identical. The guard's body
is quantified, so it is instantiated at the new body, not transported
as a derivation from the old body. -/
private theorem guardsAt (i j : Program 1) (r R d p : Program 3)
    (old : InputGuards i j r d p) : InputGuards i j R d p := by
  intro c B α Γ f u y seen
  have same (x : OTerm α) : carrier (data i j r d) false c x =
      carrier (data i j R d) false c x := rfl
  simpa only [same f,same u] using old c B α Γ f u y seen

theorem reinstall : ExactReinstallAugmentedShapeTuple := by
  intro xs s W valid i j r d v original
  obtain ⟨oldEval,_,_,cal,unique,guards,_⟩ := original
  let R := augmented i r
  obtain ⟨freshEval,freshInterp,freshRules⟩ := presentation xs s i j r d oldEval
  have base : BaseAt xs s i j R d v :=
    ⟨freshEval,freshInterp,freshRules,cal,unique,guardsAt i j r R d v.applicationGuard guards⟩
  exact exact_ReinstallShapeRefinedApplication xs s W valid i j R d v base

theorem concrete : ExactConcreteAugmentedShapeTuple := by
  intro xs s W valid
  obtain ⟨i,j,r,d,v,chosen⟩ := exact_ConcreteParsedFreshCarrierTuple xs s W valid
  have original : TupleAt xs s W i j r d v := chosen
  exact ⟨i,j,r,d,v,original,reinstall xs s W valid i j r d v original⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalAuxBottomMembershipTupleProof
