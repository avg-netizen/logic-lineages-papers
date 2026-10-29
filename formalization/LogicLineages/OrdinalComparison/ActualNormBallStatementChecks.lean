module

public import LogicLineages.OrdinalComparison.ActualNormBalls
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actual_finite_norm_balls : Targets.ActualFiniteNormBalls :=
  actualFiniteNormBalls

theorem fixed_actual_norm_ball_denotation : Targets.ActualNormBallDenotationMembership :=
  actualNormBallDenotationMembership

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
