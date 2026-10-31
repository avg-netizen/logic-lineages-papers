module
public import LogicLineages.OrdinalComparison.WWSourceSyntaxCodeCheckProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SyntaxCode.StatementChecks
 theorem checkCodeExact : Targets.CheckCodeExact := Proof.checkCodeExact
 theorem checkParserExact : Targets.CheckParserExact := Proof.checkParserExact
 theorem typedRawExact : Targets.TypedRawExact := Proof.typedRawExact
 theorem typedCheckExact : Targets.TypedCheckExact := Proof.typedCheckExact
 theorem checkPrimitiveRecursive : Targets.CheckPrimitiveRecursive := Proof.checkPrimitiveRecursive
end LogicLineages.OrdinalComparison.Source.SyntaxCode.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.Source.SyntaxCode
