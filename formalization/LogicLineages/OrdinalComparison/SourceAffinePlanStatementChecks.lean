module
public import LogicLineages.OrdinalComparison.SourceAffinePlanProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.AffinePlan.StatementChecks
 theorem addBind : Targets.AddBind := Proof.addBind
 theorem multiply : Targets.Multiply := Proof.multiply
 theorem multiplySize : Targets.MultiplySize := Proof.multiplySize
 theorem multiplyBind : Targets.MultiplyBind := Proof.multiplyBind
 theorem affine : Targets.Affine := Proof.affine
end LogicLineages.OrdinalComparison.Source.AffinePlan.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.Source.AffinePlan
