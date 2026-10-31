module
public import LogicLineages.OrdinalComparison.SourceBooleanWireProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.BooleanWire.StatementChecks
 theorem nodeExact : Targets.NodeExact := Proof.nodeExact
 theorem wireExact : Targets.WireExact := Proof.wireExact
 theorem uniqueWitnesses : Targets.UniqueWitnesses := Proof.uniqueWitnesses
 theorem rootCorrect : Targets.RootCorrect := Proof.rootCorrect
 theorem linearOverhead : Targets.LinearOverhead := Proof.linearOverhead
end LogicLineages.OrdinalComparison.Source.BooleanWire.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.Source.BooleanWire
