module
public import LogicLineages.OrdinalComparison.SourceBooleanGlobalFlattenProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.BooleanGlobalFlatten.StatementChecks
 theorem flattenExact : Targets.FlattenExact := Proof.flattenExact
 theorem sharedInputs : Targets.SharedInputs := Proof.sharedInputs
 theorem globalExact : Targets.GlobalExact := Proof.globalExact
 theorem existentialExact : Targets.ExistentialExact := Proof.existentialExact
 theorem linearOverhead : Targets.LinearOverhead := Proof.linearOverhead
end LogicLineages.OrdinalComparison.Source.BooleanGlobalFlatten.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.Source.BooleanGlobalFlatten
