module
public import LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationBinaryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationBinary.StatementChecks

theorem expansionSound : Targets.ExpansionSound := Proof.expansionSound
theorem normalizationExpansion : Targets.NormalizationExpansion := Proof.normalizationExpansion
theorem expansionTransport : Targets.ExpansionTransport := Proof.expansionTransport
theorem binaryCharacterization : Targets.BinaryCharacterization := Proof.binaryCharacterization

end LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationBinary.StatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationBinary
