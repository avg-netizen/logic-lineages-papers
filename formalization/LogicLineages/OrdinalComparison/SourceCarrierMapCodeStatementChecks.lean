module
public import LogicLineages.OrdinalComparison.SourceCarrierMapCodeTargets
public import LogicLineages.OrdinalComparison.SourceCarrierMapCodeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceCarrierMapCode.StatementChecks
theorem raw_exact : Targets.RawExact := Proof.rawExact
theorem typed_exact : Targets.TypedExact := Proof.typedExact
theorem concrete_exact : Targets.ConcreteExact := Proof.concreteExact
theorem primitive_recursive : Targets.PrimitiveRecursive := Proof.primitiveRecursive
end LogicLineages.OrdinalComparison.Source.SourceCarrierMapCode.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.Source.SourceCarrierMapCode
