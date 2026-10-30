module
public import LogicLineages.OrdinalComparison.EncodedCollapseProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_encodedTrajectoryCorrect : Targets.EncodedTrajectoryCorrect := encodedTrajectoryCorrect
theorem fixed_encodedFirstFiniteCorrect : Targets.EncodedFirstFiniteCorrect := encodedFirstFiniteCorrect
theorem fixed_encodedCollapsePartialRecursive : Targets.EncodedCollapsePartialRecursive :=
  encodedCollapsePartialRecursive
theorem fixed_encodedCollapseTotal : Targets.EncodedCollapseTotal := encodedCollapseTotal
theorem fixed_encodedCollapseSourceCorrect : Targets.EncodedCollapseSourceCorrect := encodedCollapseSourceCorrect
theorem fixed_encodedCollapseComputable : Targets.EncodedCollapseComputable := encodedCollapseComputable
theorem fixed_fullEncodedClosedEvaluation : Targets.FullEncodedClosedEvaluation := fullEncodedClosedEvaluation

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
