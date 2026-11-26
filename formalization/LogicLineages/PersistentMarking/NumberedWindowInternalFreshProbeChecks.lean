module
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.PersistentMarking.NumberedWindowTypedProbeProgramChecks
public section

namespace LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeChecks
open NumberedWindowInternalFreshProbeTargets

theorem exact_FreshProbeOutputCases : FreshProbeOutputCases :=
  NumberedWindowInternalFreshProbeProof.outputCases

theorem exact_FreshProbeRejectedExcludes : FreshProbeRejectedExcludes :=
  NumberedWindowInternalFreshProbeProof.rejectedExcludes

theorem exact_FreshProbeUnique : FreshProbeUnique :=
  NumberedWindowInternalFreshProbeProof.unique

theorem exact_OriginalFreshProbeObjectCases : ExactOriginalFreshProbeObjectCases := by
  intro s body
  obtain ⟨a,ha⟩ := (NumberedWindowTypedProbeProgramChecks.exact_TypedProbePrograms s).2
  exact ⟨a,ha,exact_FreshProbeOutputCases body a⟩

#print axioms exact_FreshProbeOutputCases
#print axioms exact_FreshProbeRejectedExcludes
#print axioms exact_FreshProbeUnique
#print axioms exact_OriginalFreshProbeObjectCases

end LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeChecks
