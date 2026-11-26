import LogicLineages.PersistentMarking.FiniteSchemaBasicChecks
import LogicLineages.PersistentMarking.FiniteSchemaRemainingChecks
namespace LogicLineages.PersistentMarking.FiniteDomainSchemaChecks
open FiniteDomainSchemaTargets
 theorem exact_FullSchema : ExtensionTest ∧ ExtensionEnumeration ∧ ExtensionDistinct ∧
    LocalSchemaExact ∧ SchemaExact ∧ SchemaKeysDistinct ∧ RestrictionKeys ∧
    RawCodeExact ∧ RawCodeDistinct ∧ ArgumentBoundCoordinates :=
  ⟨FiniteExtensionProof.test,FiniteExtensionProof.enumeration,FiniteExtensionProof.distinct,
   FiniteSchemaExactProof.localExact,FiniteSchemaExactProof.exactSchema,FiniteSchemaDistinctProof.full,
   FiniteSchemaExactProof.restrictionKeys,FiniteSchemaExactProof.rawExact,FiniteSchemaExactProof.rawDistinct,
   FiniteArgumentBoundsProof.coordinates⟩
#print axioms exact_FullSchema
end LogicLineages.PersistentMarking.FiniteDomainSchemaChecks
