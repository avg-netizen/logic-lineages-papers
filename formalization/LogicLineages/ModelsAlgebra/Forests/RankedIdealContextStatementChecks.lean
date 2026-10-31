module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealContextProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealContext.StatementChecks
 theorem embeddingReflexive : Targets.EmbeddingReflexive := Proof.embeddingReflexive
 theorem embeddingTransitive : Targets.EmbeddingTransitive := Proof.embeddingTransitive
 theorem plugMonotone : Targets.PlugMonotone := Proof.plugMonotone
 theorem holeEmbeds : Targets.HoleEmbeds := Proof.holeEmbeds
 theorem plugComposition : Targets.PlugComposition := Proof.plugComposition
end LogicLineages.ModelsAlgebra.Forests.RankedIdealContext.StatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealContext
