module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalBetaResultTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniformPackedDecodingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliaryBetaSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedDirectOperationsSupportProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalBetaResultCalibrationProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedAuxiliaryCoding
open NumberedLeastCodeRepresentative NumberedNumericDecoding NumberedDirectCertificate
open NumberedUniformPackedDecoding NumberedAuxiliarySubstitution
open InternalOriginalUniformParameterLeaves OriginalBetaResult

/-- Retain the original type component as well as the original code component.
The checked direct-rule type theorem identifies the decoded output's type;
no equality of unrelated Encodable and raw code presentations is used. -/
theorem actualOriginalBetaRawCalibration :
    OriginalBetaResultTargets.ActualOriginalBetaRawCalibration := by
  intro n arity Gamma source
  unfold rawResult
  rw [NumberedUniformPackedDecodingProof.rawPackedCalibration]
  cases hd : decodePackedNumber n arity Gamma source with
  | none => rfl
  | some q =>
    simp only [Option.map_some, Option.bind_some, packedCode]
    rw [NumberedAuxiliaryBetaSupportProof.betaCodeCalibration]
    cases hb : directTarget arity Gamma .beta q with
    | none => rfl
    | some result =>
      have ht := NumberedDirectOperationsSupportProof.directTypePreservation
        n arity Gamma .beta q result hb
      simp only [Option.map_some, Option.getD_some, packedNumber, ht]

theorem actualOriginalBetaUniformCalibration :
    OriginalBetaResultTargets.ActualOriginalBetaUniformCalibration := by
  intro n arity v
  unfold resultValue decodedValue
  cases hc : Encodable.decode (α := OrdinaryArithmeticQuotient.Context n)
      (Nat.unpair (v.get 1)).1 with
  | none => rfl
  | some ctx =>
    cases ho : parameterObject (v.get 0) (v.get 1) with
    | none => rfl
    | some obj => exact actualOriginalBetaRawCalibration n arity obj.1 obj.2

/-- The typed beta specialization has no source-window premise: this supplier
checks typing, while source membership belongs to the separate step checker. -/
theorem rawTypedBeta (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (sigma tau : Ty) (body : AuxTerm (Fin n) arity (sigma :: Gamma) tau)
    (a : AuxTerm (Fin n) arity Gamma sigma) :
    rawResult n arity Gamma
        (packedNumber (⟨tau,.app (.lam body) a⟩ : Packed (Fin n) arity Gamma)) =
      Nat.succ (packedNumber
        (⟨tau,substitute body (singleSubstitution a)⟩ : Packed (Fin n) arity Gamma)) := by
  rw [actualOriginalBetaRawCalibration,
    NumberedNumericDecodingProof.packedNumericRoundTrip]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalBetaResultCalibrationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalBetaResultCalibrationProof
