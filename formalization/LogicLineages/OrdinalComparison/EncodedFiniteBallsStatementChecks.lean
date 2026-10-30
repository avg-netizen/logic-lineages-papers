module
public import LogicLineages.OrdinalComparison.EncodedFiniteBallsProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_encodedActualNormBallImage : Targets.EncodedActualNormBallImage := encodedActualNormBallImage
theorem fixed_actualNaturalSumNormAdditive : Targets.ActualNaturalSumNormAdditive := actualNaturalSumNormAdditive
theorem fixed_fullEncodedFiniteNormBalls : Targets.FullEncodedFiniteNormBalls := fullEncodedFiniteNormBalls

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
