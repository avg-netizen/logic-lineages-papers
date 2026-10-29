module

public import LogicLineages.ModelsAlgebra.Forests.HostReductionProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.StatementChecks

theorem fixed_forbiddenAvoidanceHereditary : Targets.ForbiddenAvoidanceHereditary :=
  HostReductionProof.forbiddenAvoidanceHereditary

theorem fixed_jointImageFactorization : Targets.JointImageFactorization :=
  HostReductionProof.jointImageFactorization

theorem fixed_jointImageForest : Targets.JointImageForest :=
  HostReductionProof.jointImageForest

theorem fixed_jointImageAvoidance : Targets.JointImageAvoidance :=
  HostReductionProof.jointImageAvoidance

theorem fixed_jointImageCardBound : Targets.JointImageCardBound :=
  HostReductionProof.jointImageCardBound

theorem fixed_reducedCommonHost : Targets.ReducedCommonHost :=
  HostReductionProof.reducedCommonHost

theorem fixed_boundedCommonHost : Targets.BoundedCommonHost :=
  HostReductionProof.boundedCommonHost

end LogicLineages.ModelsAlgebra.Forests.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Forests
