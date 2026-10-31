module
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerCountVectorProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerCountVector.StatementChecks

theorem countsExact : Targets.CountsExact := Proof.countsExact
theorem lengthExact : Targets.LengthExact := Proof.lengthExact
theorem membershipExact : Targets.MembershipExact := Proof.membershipExact
theorem childrenExact : Targets.ChildrenExact := Proof.childrenExact

end LogicLineages.ModelsAlgebra.Forests.CotreePresburgerCountVector.StatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerCountVector
