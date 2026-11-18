import LogicLineages.PersistentMarking.DecisionPortsProof
namespace LogicLineages.PersistentMarking.DecisionPortsChecks
theorem exact_enumeration : DecisionPortsTargets.EnumerationExact := DecisionPortsProof.enumeration
#print axioms exact_enumeration
theorem exact_extensionRefl : DecisionPortsTargets.ExtensionReflexive := DecisionPortsProof.extensionRefl
#print axioms exact_extensionRefl
theorem exact_extensionTrans : DecisionPortsTargets.ExtensionTransitive := DecisionPortsProof.extensionTrans
#print axioms exact_extensionTrans
theorem exact_usedBound : DecisionPortsTargets.UsedBound := DecisionPortsProof.usedBound
#print axioms exact_usedBound
theorem exact_usedMono : DecisionPortsTargets.UsedMonotone := DecisionPortsProof.usedMono
#print axioms exact_usedMono
theorem exact_unused : DecisionPortsTargets.UnusedExists := DecisionPortsProof.unused
#print axioms exact_unused
theorem exact_fresh : DecisionPortsTargets.PortFresh := DecisionPortsProof.fresh
#print axioms exact_fresh
theorem exact_injective : DecisionPortsTargets.PortInjective := DecisionPortsProof.injective
#print axioms exact_injective
theorem exact_valuesExact : DecisionPortsTargets.ValuesExact := DecisionPortsProof.valuesExact
#print axioms exact_valuesExact
theorem exact_valuesTyped : DecisionPortsTargets.ValuesTyped := DecisionPortsProof.valuesTyped
#print axioms exact_valuesTyped
theorem exact_valuesWeaken : DecisionPortsTargets.ValuesWeaken := DecisionPortsProof.valuesWeaken
#print axioms exact_valuesWeaken
end LogicLineages.PersistentMarking.DecisionPortsChecks
