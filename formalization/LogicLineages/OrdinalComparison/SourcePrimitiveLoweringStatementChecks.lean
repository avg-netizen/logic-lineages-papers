module
public import LogicLineages.OrdinalComparison.SourcePrimitiveLoweringProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.PrimitiveLowering.StatementChecks
 theorem sharedInputs : Targets.SharedInputs := Proof.sharedInputs
 theorem sourceExact : Targets.SourceExact := Proof.sourceExact
 theorem primitiveRealization : Targets.PrimitiveRealization := Proof.primitiveRealization
 theorem graphExact : Targets.GraphExact := Proof.graphExact
 theorem fixedSize : Targets.FixedSize := Proof.fixedSize
end LogicLineages.OrdinalComparison.Source.PrimitiveLowering.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.Source.PrimitiveLowering
