module

public import LogicLineages.NativeModule.PersistentMarking.GraftingTargets
public import LogicLineages.NativeModule.PersistentMarking.TypeSupportNamedProof
public import LogicLineages.NativeModule.PersistentMarking.ComparisonOrdinaryProof

@[expose] public section

namespace LogicLineages.PersistentMarking.GraftingProof
open Spine NameBridge TypeSupport Grafting

theorem singleMapTyping : GraftingTargets.SingleMapTyping := by
  intro σ x p hp τ y
  by_cases he : (τ,y) = (σ,x)
  · have ht := congrArg Prod.fst he
    simp only at ht
    subst τ
    simpa only [singleMap,he,if_true] using hp
  · simp only [singleMap,he,if_false]
    exact .free

theorem typedNamedSubstitutionEncoding : GraftingTargets.TypedNamedSubstitutionEncoding := by
  intro η A τ hm hA
  have hi : FreeMapTyped EmptyContext (encodeMap η) := fun σ x => BridgeTypingProof.encodeTyped [] _ σ (hm σ x)
  have ht := FreeTypingProof.freeSubTyped EmptyContext (encodeMap η) hi (encode [] A) τ
    (BridgeTypingProof.encodeTyped [] A τ hA)
  exact DecodeRoundtripProof.encodeDecodeScoped _ (OpeningFoundationProof.typedClosedScoped _ τ ht)

theorem templateGrafting : GraftingTargets.TemplateGrafting := by
  intro S A τ σ x p q hA ho hp hq hw
  have hrelated : TwoEnvironmentTargets.Related S (singleMap σ x p) (singleMap σ x q) := by
    intro υ y
    by_cases he : (υ,y) = (σ,x)
    · simpa only [singleMap,he,if_true] using AuxiliaryEmbeddingProof.embedWeak S p q hw
    · simp only [singleMap,he,if_false]
      exact ⟨.var⟩
  have he := TwoEnvironmentProof.weak S (singleMap σ x p) (singleMap σ x q)
    (singleMapTyping σ x p hp.1) (singleMapTyping σ x q hq.1) hrelated A A
    (AuxiliaryEmbeddingProof.embedWeak S A A (ElementaryProof.ordinaryReflexive S A τ hA ho))
  obtain ⟨tree⟩ := he
  have hs := (ExtendedEndpointProof.weakFacts tree).1
  have hqo := ComparisonOrdinaryProof.weakOrdinary S p q hw
  have himages : ∀ υ y, Ordinary (singleMap σ x q υ y) := by
    intro υ y
    by_cases hh : (υ,y) = (σ,x)
    · simpa only [singleMap,hh,if_true] using hqo
    · simp only [singleMap,hh,if_false,Ordinary]
  exact ConservativeProof.weak S _ _ _ (AuxiliaryReflexivityProof.refinementRefl S _ _ hs) ⟨tree⟩
    (StructuralSubstitutionProof.ordinary (singleMap σ x q) himages 0 A ho)

theorem singleNamedTyped (σ : Ty) (x : Nat) (p : Term) (hp : NamedTyped p σ) :
    NamedMapTyped (singleNamedMap σ x p) := by
  intro τ y
  by_cases he : (τ,y) = (σ,x)
  · have ht := congrArg Prod.fst he
    simp only at ht
    subst τ
    simpa only [singleNamedMap,he,if_true] using hp
  · simp only [singleNamedMap,he,if_false]
    exact .var

theorem encodeSingle (σ : Ty) (x : Nat) (p : Term) :
    encodeMap (singleNamedMap σ x p) = singleMap σ x (encode [] p) := by
  funext τ y
  by_cases he : (τ,y) = (σ,x) <;> simp [encodeMap,singleNamedMap,singleMap,he,encode,nameLookup]

theorem namedTemplateGrafting : GraftingTargets.NamedTemplateGrafting := by
  intro S A τ σ x p q hA hvA hoA hp hvp hq hvq hw
  rw [typedNamedSubstitutionEncoding _ A τ (singleNamedTyped σ x p hp) hA,
    typedNamedSubstitutionEncoding _ A τ (singleNamedTyped σ x q hq) hA,encodeSingle,encodeSingle]
  exact templateGrafting S (encode [] A) τ σ x (encode [] p) (encode [] q)
    ⟨BridgeTypingProof.encodeTyped [] A τ hA,(BridgeTypingProof.encodeValidity S [] A).mp hvA⟩
    ((StructuralCoverageProof.encodeOrdinary [] A).mp hoA)
    ⟨BridgeTypingProof.encodeTyped [] p σ hp,(BridgeTypingProof.encodeValidity S [] p).mp hvp⟩
    ⟨BridgeTypingProof.encodeTyped [] q σ hq,(BridgeTypingProof.encodeValidity S [] q).mp hvq⟩ hw

theorem fullGrafting : GraftingTargets.FullGrafting := ⟨templateGrafting,namedTemplateGrafting⟩
end LogicLineages.PersistentMarking.GraftingProof
