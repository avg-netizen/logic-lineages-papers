import LogicLineages.PersistentMarking.MarkedFamilyBoundsProof
namespace LogicLineages.PersistentMarking.MarkedFamilyBoundsChecks
theorem exact_Join : MarkedFamilyLatticeTargets.Join := MarkedFamilyBoundsProof.join
theorem exact_Meet : MarkedFamilyLatticeTargets.Meet := MarkedFamilyBoundsProof.meet
#print axioms exact_Join
#print axioms exact_Meet
end LogicLineages.PersistentMarking.MarkedFamilyBoundsChecks
