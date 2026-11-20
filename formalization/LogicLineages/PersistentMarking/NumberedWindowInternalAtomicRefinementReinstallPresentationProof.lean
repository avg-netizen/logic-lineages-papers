module
public import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementReinstallTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementNumericChecks
import LogicLineages.PersistentMarking.NumberedWindowFormulaCalibrationChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementReinstallPresentationProof
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalAccessibilityRulesProof
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalAtomicRefinement (refined)
open NumberedWindowInternalAtomicRefinementReinstallTargets
open NumberedWindowInternalAtomicRefinementNumericChecks (exact_OriginalRefinedPresentationEvaluation)
open NumberedWindowFormulaCalibrationChecks (exact_InterpretsEvaluatingPrograms)
open NumberedWindowPresentationCheckers (checks)

theorem freshPresentation : ExactRefinedPresentationAndRules := by
  intro xs s i j r d old
  let R := refined i r
  let S := data i j R d
  have fresh := exact_OriginalRefinedPresentationEvaluation xs s i j r d old
  exact ⟨fresh,exact_InterpretsEvaluatingPrograms (checks xs s) i j R d fresh,
    ⟨actualOriginalMembershipEquation S,actualOriginalCarrierExtraction S,
      actualOriginalSuccessorClosure S,actualOriginalCertifiedSuccessorClosure S,
      actualOriginalAccessibilityIntroduction S⟩⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementReinstallPresentationProof
