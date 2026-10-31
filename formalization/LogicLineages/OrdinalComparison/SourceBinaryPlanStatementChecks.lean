module
public import LogicLineages.OrdinalComparison.SourceBinaryPlanProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.BinaryPlan.StatementChecks
 theorem renameCorrect : Targets.RenameCorrect := Proof.renameCorrect
 theorem renameSize : Targets.RenameSize := Proof.renameSize
 theorem binaryCorrect : Targets.BinaryCorrect := Proof.binaryCorrect
 theorem binarySize : Targets.BinarySize := Proof.binarySize
 theorem literalCorrect : Targets.LiteralCorrect := Proof.literalCorrect
 theorem literalSize : Targets.LiteralSize := Proof.literalSize
end LogicLineages.OrdinalComparison.Source.BinaryPlan.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.Source.BinaryPlan
