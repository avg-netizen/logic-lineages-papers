module
public import LogicLineages.OrdinalComparison.AdditiveHeadTreeTargets
public import LogicLineages.OrdinalComparison.AdditiveHeadTreeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.AdditiveHeadTree.StatementChecks
theorem head_closure_head : Targets.HeadClosureHead := Proof.headClosureHead
theorem head_closure_scalar : Targets.HeadClosureScalar := Proof.headClosureScalar
theorem ground_partial_trees : Targets.GroundPartialTrees := Proof.groundPartialTrees
theorem actual_source_trees : Targets.ActualSourceTrees := Proof.actualSourceTrees
end LogicLineages.OrdinalComparison.Source.AdditiveHeadTree.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.Source.AdditiveHeadTree
