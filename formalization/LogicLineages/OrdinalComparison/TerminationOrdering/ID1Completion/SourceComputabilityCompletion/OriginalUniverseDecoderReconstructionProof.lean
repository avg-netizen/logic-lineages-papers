module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTraversalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderContextCodecProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderCalibrationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderReconstructionProof
open Source NumberedAuxiliaryCoding NumberedAuxiliaryDecoding NumberedLeastCodeRepresentative
open OriginalUniverseDecoder OriginalUniverseDecoderEncodedProof OriginalUniverseDecoderTraversalProof
open OriginalTypedDecoder (termRequestValue requestRaw initialValue finishedValue)
open OriginalTypedDecoderExpansionProof (termRaw termMode termType)

theorem checkBit (H : Nat → Nat) (M W : Nat → Nat → Nat) (request context : Nat) :
    checkValue H M W request context = 0 ∨ checkValue H M W request context = 1 := by
  unfold checkValue finishedValue
  split <;> simp

theorem malformedContextReject (n : Nat) (H : Nat → Nat) (W : Nat → Nat → Nat)
    (typ raw gamma context : Nat)
    (hc : Encodable.decode (α := OrdinaryArithmeticQuotient.Context n) context = none) :
    checkValue H (contextMemberValue n) W (termRequestValue gamma typ raw) context = 0 := by
  unfold checkValue
  rw [termRaw,iterateSuccStart]
  simp [transitionValue,initialValue,guardValue,contextMemberValue,hc,
    Nat.add_comm 1,failedIteration,finishedValue]

/-- Reuse the accepted ALL-RAW typed decoder reconstruction after the
same-fuel inclusion, rather than selecting a new recursive semantic oracle. -/
theorem termReconstruction (n : Nat) (arity : Fin n → Nat) (typ raw gamma context : Nat) :
    checkValue (OriginalTypedDecoder.headSignatureValue n arity)
      (contextMemberValue n) (headWindowValue n arity) (termRequestValue gamma typ raw) context = 1 ↔
      ∃ (ctx : OrdinaryArithmeticQuotient.Context n) (Gamma : List Ty)
          (tau : Ty) (code : Code (Fin n)),
        Encodable.encode ctx = context ∧ Encodable.encode Gamma = gamma ∧
          typeNumber tau = typ ∧ codeNumber code = raw ∧
            NumberedUniverseRequests.valid arity ctx.1.1 ctx.1.2 (.term Gamma tau code) = true := by
  constructor
  · intro h
    cases hc : Encodable.decode (α := OrdinaryArithmeticQuotient.Context n) context with
    | none => rw [malformedContextReject n _ _ _ _ _ _ hc] at h; cases h
    | some ctx =>
      have he := OriginalUniverseDecoderContextCodecProof.outerContextDecodeSound n context ctx hc
      have ht : OriginalTypedDecoder.checkValue (OriginalTypedDecoder.headSignatureValue n arity)
          (termRequestValue gamma typ raw) = 1 :=
        acceptanceImpliesTyped _ _ _ _ _ _ h
      rw [OriginalTypedDecoderCalibrationValuesProof.termValue] at ht
      obtain ⟨Gamma,tau,code,hg,htyp,hr,hvalid⟩ :=
        (OriginalTypedDecoderCalibrationValuesProof.termReconstruction n arity typ raw gamma).mp ht
      refine ⟨ctx,Gamma,tau,code,he,hg,htyp,hr,?_⟩
      rw [← he,← hg,← htyp,← hr,termEncoded] at h
      simpa using h
  · rintro ⟨ctx,Gamma,tau,code,rfl,rfl,rfl,rfl,hv⟩
    rw [termEncoded,hv]
    rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderReconstructionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderReconstructionProof
