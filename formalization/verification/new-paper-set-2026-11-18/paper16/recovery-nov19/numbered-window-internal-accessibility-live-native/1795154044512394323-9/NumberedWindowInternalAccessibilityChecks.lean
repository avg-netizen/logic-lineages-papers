module
public import LogicLineages.PersistentMarking.NumberedWindowInternalAccessibilityTargets
import LogicLineages.PersistentMarking.NumberedWindowConcreteFormulaChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAccessibilityChecks
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesProof
open NumberedWindowInternalAccessibilityTargets NumberedWindowInternalPresentationTargets

theorem exact_ConcreteInternalAccessibility : ConcreteInternalAccessibility := by
  intro xs s
  obtain ⟨i,j,r,d,heval,hinterp⟩ :=
    NumberedWindowConcreteFormulaChecks.exact_ConcretePresentation xs s
  let p := data i j r d
  refine ⟨i,j,r,d,heval,hinterp,?_⟩
  exact ⟨actualOriginalMembershipEquation p, actualOriginalCarrierExtraction p,
    actualOriginalSuccessorClosure p, actualOriginalCertifiedSuccessorClosure p,
    actualOriginalAccessibilityIntroduction p⟩

#print axioms exact_ConcreteInternalAccessibility
end LogicLineages.PersistentMarking.NumberedWindowInternalAccessibilityChecks
