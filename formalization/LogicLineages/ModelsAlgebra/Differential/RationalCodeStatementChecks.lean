module

public import LogicLineages.ModelsAlgebra.Differential.RationalCode
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.StatementChecks

theorem fixed_rationalCodeCoverage : Targets.rationalCodeCoverage := RationalCode.coverage
theorem fixed_rationalCodeCorrect : Targets.rationalCodeCorrect := RationalCode.arithmetic_correct
theorem fixed_rationalCodePrimitiveRecursive : Targets.rationalCodePrimitiveRecursive :=
  RationalCode.arithmetic_primitive_recursive
theorem fixed_rationalCodeRoundtrip : Targets.rationalCodeRoundtrip := RationalCode.codec_roundtrip

end LogicLineages.ModelsAlgebra.Differential.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Differential
