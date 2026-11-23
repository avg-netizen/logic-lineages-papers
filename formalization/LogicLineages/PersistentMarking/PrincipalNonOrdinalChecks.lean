import LogicLineages.PersistentMarking.PrincipalNonOrdinalProof

namespace LogicLineages.PersistentMarking.PrincipalNonOrdinalChecks
open PrincipalNonOrdinalTargets

theorem exact_Decision : Decision := PrincipalNonOrdinalProof.decision
theorem exact_OrderLaws : OrderLaws := PrincipalNonOrdinalProof.orderLaws
theorem exact_Structural : Structural := PrincipalNonOrdinalProof.structural
theorem exact_Orientation : Orientation := PrincipalNonOrdinalProof.orientation
theorem exact_Ranked : Ranked := PrincipalNonOrdinalProof.ranked
theorem exact_PrincipalNonOrdinal : PrincipalNonOrdinal := PrincipalNonOrdinalProof.principalNonOrdinal

#print axioms exact_Decision
#print axioms exact_OrderLaws
#print axioms exact_Structural
#print axioms exact_Orientation
#print axioms exact_Ranked
#print axioms exact_PrincipalNonOrdinal

end LogicLineages.PersistentMarking.PrincipalNonOrdinalChecks
