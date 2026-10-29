module
public import LogicLineages.OrdinalComparison.NaturalProductInterpretation
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.CheckedNaturalProduct

theorem actual_source_natural_product_denotation :
    Targets.NaturalProductDenotation naturalProduct := naturalProductDenotation

theorem actual_source_natural_product_norm_bound :
    Targets.NaturalProductNormBound naturalProduct := naturalProductNormBound

end LogicLineages.OrdinalComparison.CheckedNaturalProduct

#audit_namespace LogicLineages.OrdinalComparison
