module
public import LogicLineages.ModelsAlgebra.PGroups.DirectSumUlmProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.DirectSumUlmStatementChecks
theorem layerEquivalence : Targets.transfiniteDirectSumUlm.{u,v,w} := transfinite_direct_sum_ulm
theorem rankSum : Targets.transfiniteDirectSumUlmRank.{u,v,w} := transfinite_direct_sum_ulm_rank
end LogicLineages.ModelsAlgebra.PGroups.DirectSumUlmStatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.PGroups.DirectSumUlmStatementChecks
