module

public import LogicLineages.NativeModule.PersistentMarking.TypeSupportSubstitutionProof
public import LogicLineages.NativeModule.PersistentMarking.StructuralCoverageProof
public import LogicLineages.NativeModule.PersistentMarking.DecodeRoundtripProof

@[expose] public section

namespace LogicLineages.PersistentMarking.TypeSupportNamedProof
open Spine NameBridge TypeSupport TypeSupportFoundationProof

theorem mapOrdinary (S : Signature) (η : NamedMap) (h : NamedOrdinaryMap S η) :
    StructuralStabilityTargets.OrdinaryMap S (encodeMap η) := by
  intro σ x
  exact ⟨⟨BridgeTypingProof.encodeTyped [] _ σ (h σ x).1,
    (BridgeTypingProof.encodeValidity S [] _).mp (h σ x).2.1⟩,
    (StructuralCoverageProof.encodeOrdinary [] _).mp (h σ x).2.2⟩

theorem namedSubstitutionEncoding : TypeSupportTargets.NamedSubstitutionEncoding := by
  intro S η q τ hm hq _ _
  have hi : FreeMapTyped EmptyContext (encodeMap η) := fun σ x => (mapOrdinary S η hm σ x).1.1
  have ht := FreeTypingProof.freeSubTyped EmptyContext (encodeMap η) hi (encode [] q) τ
    (BridgeTypingProof.encodeTyped [] q τ hq)
  exact DecodeRoundtripProof.encodeDecodeScoped _ (OpeningFoundationProof.typedClosedScoped _ τ ht)

theorem namedExactSubstitution : TypeSupportTargets.NamedExactSubstitution := by
  intro S η q τ hm hq hv ho ρ
  have hp : PaperTerm S (encode [] q) τ := ⟨BridgeTypingProof.encodeTyped [] q τ hq,
    (BridgeTypingProof.encodeValidity S [] q).mp hv⟩
  have he := TypeSupportSubstitutionProof.exactSubstitution S (encode [] q) τ (encodeMap η) hp
    ((StructuralCoverageProof.encodeOrdinary [] q).mp ho) (mapOrdinary S η hm) ρ
  rw [← encodingSupport [] (namedSubstitute η q),namedSubstitutionEncoding S η q τ hm hq hv ho]
  simpa only [ImageSupport,encodeMap,encodingSupport] using he
end LogicLineages.PersistentMarking.TypeSupportNamedProof
