import LogicLineages.PersistentMarking.FiniteSchemaExactProof
namespace LogicLineages.PersistentMarking.FiniteSchemaBasicChecks
 theorem exact_ExtensionTest : FiniteDomainSchemaTargets.ExtensionTest := FiniteExtensionProof.test
 theorem exact_ExtensionEnumeration : FiniteDomainSchemaTargets.ExtensionEnumeration := FiniteExtensionProof.enumeration
 theorem exact_ExtensionDistinct : FiniteDomainSchemaTargets.ExtensionDistinct := FiniteExtensionProof.distinct
 theorem exact_LocalSchemaExact : FiniteDomainSchemaTargets.LocalSchemaExact := FiniteSchemaExactProof.localExact
 theorem exact_SchemaExact : FiniteDomainSchemaTargets.SchemaExact := FiniteSchemaExactProof.exactSchema
 theorem exact_RestrictionKeys : FiniteDomainSchemaTargets.RestrictionKeys := FiniteSchemaExactProof.restrictionKeys
 theorem exact_RawCodeExact : FiniteDomainSchemaTargets.RawCodeExact := FiniteSchemaExactProof.rawExact
 theorem exact_RawCodeDistinct : FiniteDomainSchemaTargets.RawCodeDistinct := FiniteSchemaExactProof.rawDistinct
#print axioms exact_ExtensionTest
#print axioms exact_ExtensionEnumeration
#print axioms exact_ExtensionDistinct
#print axioms exact_LocalSchemaExact
#print axioms exact_SchemaExact
#print axioms exact_RestrictionKeys
#print axioms exact_RawCodeExact
#print axioms exact_RawCodeDistinct
end LogicLineages.PersistentMarking.FiniteSchemaBasicChecks
