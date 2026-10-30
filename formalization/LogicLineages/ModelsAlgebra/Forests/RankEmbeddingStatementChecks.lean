module

public import LogicLineages.ModelsAlgebra.Forests.RankEmbeddingProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.StatementChecks

theorem clusterRankEmbedding : LogicLineages.ModelsAlgebra.Forests.Targets.ClusterRankEmbedding :=
  LogicLineages.ModelsAlgebra.Forests.RankEmbeddingProof.clusterRankEmbedding

end LogicLineages.ModelsAlgebra.Forests.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Forests
