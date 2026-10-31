module
public import LogicLineages.ModelsAlgebra.PGroups.PrimaryZeroSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.PrimaryZeroSyntaxStatementChecks
theorem primaryAxioms : Targets.primarySentenceExact := primary_sentence_exact
theorem zeroStage : Targets.zeroStageDescriptor := zero_stage_descriptor
end LogicLineages.ModelsAlgebra.PGroups.PrimaryZeroSyntaxStatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.PGroups.PrimaryZeroSyntaxStatementChecks
