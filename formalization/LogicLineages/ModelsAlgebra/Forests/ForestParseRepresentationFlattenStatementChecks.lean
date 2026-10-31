module
public import LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationFlattenProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationFlatten.StatementChecks

theorem mergeCorrect : Targets.MergeCorrect := Proof.mergeCorrect

theorem binaryReducedRepresentation : Targets.BinaryReducedRepresentation := Proof.binaryReducedRepresentation

theorem normalizationCanonical : Targets.NormalizationCanonical := Proof.normalizationCanonical

end LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationFlatten.StatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationFlatten
