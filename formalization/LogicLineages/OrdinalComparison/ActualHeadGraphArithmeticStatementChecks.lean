module
public import LogicLineages.OrdinalComparison.ActualHeadGraphArithmeticProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ActualHeadGraph.Arithmetic.StatementChecks
 theorem fixed_full_phi : Targets.FullPhiGate := Proof.fullPhiGate
 theorem fixed_phi_chain : Targets.FixedPhiChain := Proof.fixedPhiChain
 theorem fixed_unit_expansion : Targets.UnitTreeExpansion := Proof.unitTreeExpansion
end LogicLineages.OrdinalComparison.Source.ActualHeadGraph.Arithmetic.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.Source.ActualHeadGraph.Arithmetic
