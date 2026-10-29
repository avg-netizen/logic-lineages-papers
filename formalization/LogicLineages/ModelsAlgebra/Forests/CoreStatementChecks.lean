module

public import LogicLineages.ModelsAlgebra.Forests.CoreTargets
public import LogicLineages.ModelsAlgebra.Forests.CoreFacts
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.CoreStatementChecks

theorem incomparableNoCommonUpper : CoreTargets.incomparableNoCommonUpper := by
  intro α r h x y hxy
  exact Core.incomparable_no_common_upper h hxy

theorem embeddingPreservesForest : CoreTargets.embeddingPreservesForest := by
  intro α β r s f hf hs
  exact Core.predChain_pullback f hf hs

theorem embeddingPreservesComparabilityGraph :
    CoreTargets.embeddingPreservesComparabilityGraph := by
  intro α β r s f hf
  exact Core.comparableAdj_embedding f hf

end LogicLineages.ModelsAlgebra.Forests.CoreStatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.Forests.Core
#audit_namespace LogicLineages.ModelsAlgebra.Forests.CoreStatementChecks
