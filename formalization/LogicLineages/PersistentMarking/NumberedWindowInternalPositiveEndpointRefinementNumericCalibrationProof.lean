module
public import LogicLineages.PersistentMarking.NumberedWindowInternalPositiveEndpointRefinementNumericTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalPositiveEndpointRefinementNumericControlProof
import LogicLineages.PersistentMarking.NumberedWindowConcretePositiveEndpointsChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalPositiveEndpointRefinementNumericCalibrationProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open NumberedWindowInternalPositiveEndpointRefinementNumericTargets
open NumberedWindowInternalPositiveEndpointRefinementNumericControlProof (numericBranches)
open NumberedWindowConcretePositiveEndpointsChecks (exact_ConcretePositiveScalarEndpoints)
open NumberedWindowConcreteCheckers (positive)

theorem originalPositive : ExactOriginalPositiveEndpointRefinement := by
  intro entries s i r oldScalar oldPositive x w y
  rw [numericBranches i r x w y,oldPositive x w y]
  cases accepted : positive entries s x w y with
  | false => simp [accepted]
  | true =>
    have carriers := exact_ConcretePositiveScalarEndpoints entries s x w y accepted
    simp [accepted,oldScalar,carriers.1,carriers.2]

theorem originalEvaluation : ExactOriginalPositiveEndpointPresentationEvaluation := by
  intro entries s i j r d old
  exact ⟨old.1,old.2.1,originalPositive entries s i r old.1 old.2.2.1,old.2.2.2⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalPositiveEndpointRefinementNumericCalibrationProof
