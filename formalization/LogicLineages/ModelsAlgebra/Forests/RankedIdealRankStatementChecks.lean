module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealRankProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealRank.StatementChecks
 theorem reachReflexive : Targets.ReachReflexive := Proof.reachReflexive
 theorem reachTransitive : Targets.ReachTransitive := Proof.reachTransitive
 theorem componentRank : Targets.ComponentRank := Proof.componentRank
 theorem lowerRank : Targets.LowerRank := Proof.lowerRank
 theorem predecessorCases : Targets.PredecessorCases := Proof.predecessorCases
 theorem linearChildren : Targets.LinearChildren := Proof.linearChildren
end LogicLineages.ModelsAlgebra.Forests.RankedIdealRank.StatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealRank
