module
public import LogicLineages.PersistentMarking.NumberedWindowInternalPositiveEndpointRefinementTupleTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalPositiveEndpointRefinementNumericChecks
import LogicLineages.PersistentMarking.NumberedWindowFormulaCalibrationChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalPositiveEndpointRefinementTuplePresentationProof
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalAccessibilityRulesProof
open NumberedWindowFormulaCalibrationTargets (Evaluates)
open NumberedWindowFormulaCalibrationChecks (exact_InterpretsEvaluatingPrograms)
open NumberedWindowPresentationCheckers (checks)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalPositiveEndpointRefinement (withEndpointCarriers)
open NumberedWindowInternalPositiveEndpointRefinementNumericChecks
  (exact_OriginalPositiveEndpointPresentationEvaluation)
open NumberedWindowInternalPositiveEndpointRefinementTupleTargets

theorem freshPresentation : ExactEndpointRefinedPresentation := by
  intro xs s i j r d old
  let R := withEndpointCarriers i r
  let S := data i j R d
  have values : Evaluates (checks xs s) i j R d :=
    exact_OriginalPositiveEndpointPresentationEvaluation xs s i j r d old
  exact ⟨values,exact_InterpretsEvaluatingPrograms (checks xs s) i j R d values,
    ⟨actualOriginalMembershipEquation S,actualOriginalCarrierExtraction S,
      actualOriginalSuccessorClosure S,actualOriginalCertifiedSuccessorClosure S,
      actualOriginalAccessibilityIntroduction S⟩⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalPositiveEndpointRefinementTuplePresentationProof
