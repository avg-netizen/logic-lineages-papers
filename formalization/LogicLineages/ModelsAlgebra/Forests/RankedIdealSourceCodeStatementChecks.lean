module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealSourceCodeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealSourceCode.StatementChecks
 theorem sourceCodeExact : Targets.SourceCodeExact := Proof.sourceCodeExact
 theorem sourceCoverIdeals : Targets.SourceCoverIdeals := Proof.sourceCoverIdeals
 theorem sourceCoverExact : Targets.SourceCoverExact := Proof.sourceCoverExact
 theorem sourceCoverEmpty : Targets.SourceCoverEmpty := Proof.sourceCoverEmpty
end LogicLineages.ModelsAlgebra.Forests.RankedIdealSourceCode.StatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealSourceCode
