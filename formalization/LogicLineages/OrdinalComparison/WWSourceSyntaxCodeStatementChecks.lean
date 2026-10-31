module
public import LogicLineages.OrdinalComparison.WWSourceSyntaxCodeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SyntaxCode.StatementChecks
 theorem decodeEncode : Targets.DecodeEncode := Proof.decodeEncode
 theorem encodeDecode : Targets.EncodeDecode := Proof.encodeDecode
 theorem codeInjective : Targets.CodeInjective := Proof.codeInjective
 theorem constructorsPrimitiveRecursive : Targets.ConstructorsPrimitiveRecursive := Proof.constructorsPrimitiveRecursive
end LogicLineages.OrdinalComparison.Source.SyntaxCode.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.Source.SyntaxCode
