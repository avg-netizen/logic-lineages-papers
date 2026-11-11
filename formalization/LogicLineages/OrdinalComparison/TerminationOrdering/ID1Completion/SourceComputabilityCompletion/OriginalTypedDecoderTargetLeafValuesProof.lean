module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderCodecProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniformPackedDecodingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTargetLeafValuesProof
open Source OriginalTypedDecoder OriginalTypedDecoderCodecProof
open InternalOriginalUniformParameterLeaves NumberedNumericDecoding

theorem parameterObjectEncoded (value parameter : Nat) (Gamma : List Ty)
    (hg : Encodable.encode Gamma = (Nat.unpair parameter).2) :
    parameterObject value parameter = some (Gamma,value) := by
  rw [parameterObject,← hg]
  change Encodable.decode (Encodable.encode (Gamma,value)) = some (Gamma,value)
  exact Encodable.encodek _

theorem targetValueEquation (n : Nat) (arity : Fin n → Nat) (v : List.Vector Nat 2) :
    targetValue n arity v =
      if (Encodable.decode (α := OrdinaryArithmeticQuotient.Context n)
          (Nat.unpair (v.get 1)).1).isSome = true then
        packedDecoderValue n arity (v.get 0) (Nat.unpair (v.get 1)).2
      else 0 := by
  obtain ⟨Gamma,hg⟩ := contextEncodingSurjective (Nat.unpair (v.get 1)).2
  have ho := parameterObjectEncoded (v.get 0) (v.get 1) Gamma hg
  cases hc : Encodable.decode (α := OrdinaryArithmeticQuotient.Context n)
      (Nat.unpair (v.get 1)).1 with
  | none => simp [targetValue,decodedValue,hc]
  | some context =>
    simp only [targetValue,decodedValue,hc,ho]
    rw [← hg,NumberedUniformPackedDecodingProof.rawPackedCalibration n arity Gamma (v.get 0)]
    simp [packedDecoderValue,Encodable.encodek]

theorem packedBit (n : Nat) (arity : Fin n → Nat) (value gamma : Nat) :
    packedDecoderValue n arity value gamma = 0 ∨
      packedDecoderValue n arity value gamma = 1 := by
  unfold packedDecoderValue
  cases Encodable.decode (α := List Ty) gamma with
  | none => exact Or.inl rfl
  | some Gamma =>
    cases hc : decodePackedNumber n arity Gamma value <;> simp [hc]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTargetLeafValuesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTargetLeafValuesProof
