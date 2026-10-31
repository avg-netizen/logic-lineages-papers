module
public import LogicLineages.ModelsAlgebra.PGroups.LocalSocleBFProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.LocalSocleBFStatementChecks
theorem localSocleComparison : Targets.localSocleBackForth := local_socle_back_forth
theorem reducedLongComparison : Targets.reducedLongBackForth := reduced_long_back_forth
theorem reducedLimitCut : Targets.reducedLimitCutComparison := reduced_limit_cut_comparison
end LogicLineages.ModelsAlgebra.PGroups.LocalSocleBFStatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.PGroups.LocalSocleBFStatementChecks
