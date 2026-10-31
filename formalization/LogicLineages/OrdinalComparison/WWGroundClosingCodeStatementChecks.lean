module
public import LogicLineages.OrdinalComparison.WWGroundClosingCodeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.GroundClosingCode.StatementChecks
 theorem primitiveRecursive : Targets.PrimitiveRecursive := Proof.primitiveRecursive
 theorem rawExact : Targets.RawExact := Proof.rawExact
 theorem typedExact : Targets.TypedExact := Proof.typedExact
 theorem closedExact : Targets.ClosedExact := Proof.closedExact
end LogicLineages.OrdinalComparison.Source.GroundClosingCode.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.Source.GroundClosingCode
