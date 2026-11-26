import LogicLineages.PersistentMarking.MarkedExtrasEnumerationProof
import LogicLineages.PersistentMarking.MarkedExtrasWeakeningProof
namespace LogicLineages.PersistentMarking.MarkedExtrasChecks
theorem exact_UniverseExact : MarkedExtrasTargets.UniverseExact := MarkedExtrasFoundationProof.universeExact
theorem exact_UniverseDistinct : MarkedExtrasTargets.UniverseDistinct := MarkedExtrasFoundationProof.distinct
theorem exact_TaggedOrder : MarkedExtrasTargets.TaggedOrder := MarkedExtrasFoundationProof.order
theorem exact_DownExact : MarkedExtrasTargets.DownExact := MarkedExtrasFoundationProof.downExact
theorem exact_DownIsExtra : MarkedExtrasTargets.DownIsExtra := MarkedExtrasDownProof.downExtra
theorem exact_DownIdentity : MarkedExtrasTargets.DownIdentity := MarkedExtrasDownProof.downIdentity
theorem exact_Enumeration : MarkedExtrasTargets.Enumeration := MarkedExtrasEnumerationProof.enumeration
theorem exact_RestrictionMonotone : MarkedExtrasTargets.RestrictionMonotone := MarkedExtrasRestrictionProof.monotone
theorem exact_Weakening : MarkedExtrasTargets.Weakening := MarkedExtrasRestrictionProof.weakening
theorem exact_WeakeningAlgebra : MarkedExtrasTargets.WeakeningAlgebra := MarkedExtrasWeakeningProof.algebra
#print axioms exact_UniverseExact
#print axioms exact_UniverseDistinct
#print axioms exact_TaggedOrder
#print axioms exact_DownExact
#print axioms exact_DownIsExtra
#print axioms exact_DownIdentity
#print axioms exact_Enumeration
#print axioms exact_RestrictionMonotone
#print axioms exact_Weakening
#print axioms exact_WeakeningAlgebra
end LogicLineages.PersistentMarking.MarkedExtrasChecks
