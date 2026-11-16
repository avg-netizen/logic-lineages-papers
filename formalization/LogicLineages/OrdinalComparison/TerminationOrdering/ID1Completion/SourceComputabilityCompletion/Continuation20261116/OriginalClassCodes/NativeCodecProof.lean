module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.NativeFrontendProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentCandidate.NativeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.NativeCodecProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open OrdinaryArithmeticQuotientDecoderProof
open NumberedMultisetNumeric NumberedLeastCodeRepresentative
open Continuation20261114 Continuation20261115

theorem productCanonical {A B : Type} [Encodable A] [Encodable B]
    (ha : Canonical A inferInstance) (hb : Canonical B inferInstance) :
    Canonical (A × B) inferInstance := by
  intro raw obj h
  rw [Encodable.decode_prod_val] at h
  obtain ⟨a,ha',h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨bb,hb',he⟩ := Option.map_eq_some_iff.mp h
  cases he
  rw [Encodable.encode_prod_val,ha _ _ ha',hb _ _ hb',Nat.pair_unpair]

theorem contextCanonical (n : Nat) : Canonical (OrdinaryArithmeticQuotient.Context n) inferInstance :=
  productCanonical
    (productCanonical (canonicalList _ (canonicalFin n))
      OriginalTypedDecoderCodecProof.contextDecodeSound)
    (tableCanonical n)

theorem symbolNumbers (n : Nat) (xs : List (Fin n)) :
    Encodable.encode xs = numbersNumber (xs.map Fin.val) := by
  rw [OriginalTypeListsEnumeration.CodecProof.listEncoding]
  rfl

theorem inputOriginal (n : Nat) (ctx : OrdinaryArithmeticQuotient.Context n)
    (Gamma : List Source.Ty) (q : NumberedUniformPackedDecoding.RawPacked n) :
    NativeSelectorsProof.input (Encodable.encode q.1) (codeNumber q.2)
      (numbersNumber (ctx.1.1.map Fin.val)) (numbersNumber (ctx.1.2.map typeNumber))
      (Encodable.encode ctx.2) (Encodable.encode Gamma) =
    ofFn ![Encodable.encode q,Nat.pair (Encodable.encode ctx) (Encodable.encode Gamma)] := by
  rw [← symbolNumbers,← OriginalContextInsertionCalibrationProof.contextNumbers]
  rfl

theorem frontendOriginal (n : Nat) (arity : Fin n → Nat)
    (ctx : OrdinaryArithmeticQuotient.Context n) (Gamma : List Source.Ty)
    (q : NumberedUniformPackedDecoding.RawPacked n) :
    evaluate (frontend n arity)
      (ofFn ![Encodable.encode q,Nat.pair (Encodable.encode ctx) (Encodable.encode Gamma)]) =
    TwoSol20261113.CalibratedPrimary.Membership.entriesCode
      (ContextUniformPrimary.classCodes arity ctx.1.1 ctx.1.2 Gamma q) := by
  rw [← inputOriginal]
  exact NativeFrontendProof.frontendValue n arity _ _ _ _ _
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.NativeCodecProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.NativeCodecProof
