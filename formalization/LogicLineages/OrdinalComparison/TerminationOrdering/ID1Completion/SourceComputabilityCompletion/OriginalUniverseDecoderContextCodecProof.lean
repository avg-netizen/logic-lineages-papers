module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderCodecProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticQuotientDecoderProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderContextCodecProof
open Source OriginalUniverseDecoder OrdinaryArithmeticQuotientDecoderProof

/-- Product canonicity uses the original two decoders, not a replacement code. -/
theorem canonicalProduct {A B : Type} (a : Encodable A) (b : Encodable B)
    (ha : Canonical A a) (hb : Canonical B b) :
    Canonical (A × B) (@Encodable.Prod.encodable A B a b) := by
  intro value pair h
  rw [Encodable.decode_prod_val] at h
  obtain ⟨x,hx,hrest⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨y,hy,heq⟩ := Option.map_eq_some_iff.mp hrest
  subst pair
  change Nat.pair (@Encodable.encode A a x) (@Encodable.encode B b y) = value
  rw [ha _ _ hx,hb _ _ hy,Nat.pair_unpair]

/-- The ORIGINAL Context includes the canonical finite dependent-function
encoding of its table. No Primcodable.finArrow codec is substituted. -/
theorem outerContextDecodeSound (n value : Nat) (ctx : OrdinaryArithmeticQuotient.Context n)
    (h : Encodable.decode (α := OrdinaryArithmeticQuotient.Context n) value = some ctx) :
    Encodable.encode ctx = value := by
  have hs : Canonical (List (Fin n)) inferInstance :=
    canonicalList _ (canonicalFin n)
  have ht : Canonical (List Ty) inferInstance := OriginalTypedDecoderCodecProof.contextDecodeSound
  exact canonicalProduct _ _ (canonicalProduct _ _ hs ht) (tableCanonical n) value ctx h

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderContextCodecProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderContextCodecProof
