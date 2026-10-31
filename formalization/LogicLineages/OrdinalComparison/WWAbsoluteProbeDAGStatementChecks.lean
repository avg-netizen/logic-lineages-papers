module
public import LogicLineages.OrdinalComparison.WWAbsoluteProbeDAGProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.AbsoluteProbeDAG.StatementChecks
 theorem substitution : Targets.Substitution := Proof.substitution
 theorem closing : Targets.Closing := Proof.closing
 theorem probe : Targets.Probe := Proof.probe
 theorem original : Targets.Original := Proof.original
 theorem closed : Targets.Closed := Proof.closed
end LogicLineages.OrdinalComparison.Source.AbsoluteProbeDAG.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.Source.AbsoluteProbeDAG
