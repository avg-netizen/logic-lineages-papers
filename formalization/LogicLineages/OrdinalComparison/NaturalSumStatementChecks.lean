module
public import LogicLineages.OrdinalComparison.NaturalSumInterpretation
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.CheckedNaturalSum

theorem exact_collected_cantor_coefficients :
    Targets.NaturalSumCoefficients naturalSum := naturalSumCoefficients

theorem exact_source_additive_norm :
    Targets.NaturalSumNormAdditive naturalSum := naturalSumNormAdditive

theorem actual_ordinal_cantor_coefficients :
    Targets.NaturalSumOrdinalCoefficients naturalSum := naturalSumOrdinalCoefficients

theorem actual_source_natural_sum_denotation :
    Targets.NaturalSumDenotation naturalSum := naturalSumDenotation

end LogicLineages.OrdinalComparison.CheckedNaturalSum

#audit_namespace LogicLineages.OrdinalComparison
