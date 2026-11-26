import LogicLineages.PersistentMarking.Paper16StructuralScopeTargets
import LogicLineages.PersistentMarking.ProtectedSpineFreeSubstitutionProof
import LogicLineages.PersistentMarking.ProtectedSpineBoundSubstitutionProof
import LogicLineages.PersistentMarking.ProtectedSpineApplicationGapChecks

namespace LogicLineages.PersistentMarking.Paper16StructuralScopeProof
open Spine NameBridge TypeSupport Grafting Paper16StructuralScopeTargets

theorem exact_NamedValueSubstitution : NamedValueSubstitution := by
  intro S E H M η q σ names hPrefix retained _support ordinary images typed covered
  have mapTyped : NamedMapTyped η := fun τ x => (ordinary τ x).1
  have encoded : Typed EmptyContext (encode [] q) σ :=
    BridgeTypingProof.encodeTyped [] q σ typed
  rw [GraftingProof.typedNamedSubstitutionEncoding η q σ mapTyped typed]
  exact ProtectedSpineFreeSubstitutionProof.exact_FreeSubstitution
    S E H M (encodeMap η) EmptyContext (encode [] q) σ 0 hPrefix retained images encoded covered

/-- The manuscript's structural interpretation with the fixed-point
hypothesis and the bottom-family obstruction. -/
theorem exact_StructuralInterpretationWithBoundary : StructuralInterpretationWithBoundary :=
  ⟨⟨ProtectedSpineInterpretationProof.exact_InterpretationLaws,
    ProtectedSpineFreeSubstitutionProof.exact_FreeSubstitution,
    ProtectedSpineBoundSubstitutionProof.exact_BoundSubstitution,
    exact_NamedValueSubstitution,
    ProtectedSpineNamedConcreteCallProof.exact_NamedFixedConcreteWholeCall,
    ProtectedSpineFiniteConcreteEnvironmentProof.exact_CanonicalNamedWholeCall,
    ProtectedSpineFiniteConcreteEnvironmentProof.exact_CanonicalConcretePrefixCall⟩,
    ProtectedSpineApplicationGapChecks.exact_AvailabilityGap⟩

#print axioms exact_NamedValueSubstitution
#print axioms exact_StructuralInterpretationWithBoundary

end LogicLineages.PersistentMarking.Paper16StructuralScopeProof
