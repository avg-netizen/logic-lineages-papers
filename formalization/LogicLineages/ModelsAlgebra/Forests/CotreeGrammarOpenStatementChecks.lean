module
public import LogicLineages.ModelsAlgebra.Forests.CotreeGrammarOpenProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreeGrammarOpen.StatementChecks

theorem treeBalance : Targets.TreeBalance := Proof.treeBalance

theorem treeTerminals : Targets.TreeTerminals := Proof.treeTerminals

theorem closedBuilds : Targets.ClosedBuilds := Proof.closedBuilds

theorem buildsClosedTree : Targets.BuildsClosedTree := Proof.buildsClosedTree

theorem plugCounts : Targets.PlugCounts := Proof.plugCounts

theorem holeFactorization : Targets.HoleFactorization := Proof.holeFactorization

end LogicLineages.ModelsAlgebra.Forests.CotreeGrammarOpen.StatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.Forests.CotreeGrammarOpen
