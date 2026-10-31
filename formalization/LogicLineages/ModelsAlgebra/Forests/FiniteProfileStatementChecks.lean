module
public import LogicLineages.ModelsAlgebra.Forests.FiniteProfileProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.FiniteProfile.StatementChecks

theorem leafExact : Targets.LeafExact := Proof.leafExact

theorem splitEmbedding : Targets.SplitEmbedding := Proof.splitEmbedding

theorem runExact : Targets.RunExact := Proof.runExact

theorem acceptanceExact : Targets.AcceptanceExact := Proof.acceptanceExact

theorem avoidanceDownward : Targets.AvoidanceDownward := Proof.avoidanceDownward

end LogicLineages.ModelsAlgebra.Forests.FiniteProfile.StatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.Forests.FiniteProfile
