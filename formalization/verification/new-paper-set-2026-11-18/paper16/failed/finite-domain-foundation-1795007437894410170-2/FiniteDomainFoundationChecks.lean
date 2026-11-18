import LogicLineages.PersistentMarking.FiniteEqualityProof
import LogicLineages.PersistentMarking.FinitePrefixProof
import LogicLineages.PersistentMarking.FiniteVectorProof
namespace LogicLineages.PersistentMarking.FiniteDomainFoundationChecks
 theorem exact_ExprEquality : FiniteDomainFoundationTargets.ExprEquality := FiniteEqualityProof.expr
 theorem exact_ArgsEquality : FiniteDomainFoundationTargets.ArgsEquality := FiniteEqualityProof.args
 theorem exact_ObservationDedup : FiniteDomainFoundationTargets.ObservationDedup := FiniteEqualityProof.observations
 theorem exact_ContextDedup : FiniteDomainFoundationTargets.ContextDedup := FiniteEqualityProof.contexts
 theorem exact_PrefixExact : FiniteDomainFoundationTargets.PrefixExact := FinitePrefixProof.exactPrefix
 theorem exact_PrefixProper : FiniteDomainFoundationTargets.PrefixProper := FinitePrefixProof.proper
 theorem exact_PrefixDistinct : FiniteDomainFoundationTargets.PrefixDistinct := FinitePrefixProof.distinct
 theorem exact_VectorExact : FiniteDomainFoundationTargets.VectorExact := FiniteVectorProof.exactVector
 theorem exact_VectorDistinct : FiniteDomainFoundationTargets.VectorDistinct := FiniteVectorProof.distinct
 theorem exact_VectorCoordinates : FiniteDomainFoundationTargets.VectorCoordinates := FiniteVectorProof.coordinates
 theorem exact_EmptyAndZero : FiniteDomainFoundationTargets.EmptyAndZero := FiniteVectorProof.emptyZero
#print axioms exact_ExprEquality
#print axioms exact_ArgsEquality
#print axioms exact_ObservationDedup
#print axioms exact_ContextDedup
#print axioms exact_PrefixExact
#print axioms exact_PrefixProper
#print axioms exact_PrefixDistinct
#print axioms exact_VectorExact
#print axioms exact_VectorDistinct
#print axioms exact_VectorCoordinates
#print axioms exact_EmptyAndZero
end LogicLineages.PersistentMarking.FiniteDomainFoundationChecks
