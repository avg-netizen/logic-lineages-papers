module
public import LogicLineages.OrdinalComparison.NormBalls
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.CheckedNormBalls

theorem all_normal_inputs_finite : Targets.FiniteNormalNormBalls :=
  finiteNormalNormBalls

theorem exact_executable_norm_ball_membership :
    Targets.ExactNormalNormEnumerator notationNormBall := notationNormBall_exact

end LogicLineages.OrdinalComparison.CheckedNormBalls

#audit_namespace LogicLineages.OrdinalComparison
