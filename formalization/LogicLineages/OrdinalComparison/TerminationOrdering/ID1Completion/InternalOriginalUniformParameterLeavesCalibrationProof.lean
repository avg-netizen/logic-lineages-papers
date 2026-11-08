module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformParameterLeavesTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ContextUniformPrimaryCalibrationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformParameterLeavesCalibrationProof
open Source InternalOriginalUniformParameterLeaves

theorem targetCalibration (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (value : Nat) :
    (NumberedUniformPackedDecoding.rawPackedDecode n arity Gamma value).isSome.toNat =
      InternalOriginalStepGuard.targetValidityValue n arity Gamma value := by
  rw [NumberedUniformPackedDecodingProof.rawPackedCalibration]
  unfold InternalOriginalStepGuard.targetValidityValue
  cases NumberedNumericDecoding.decodePackedNumber n arity Gamma value <;> rfl

theorem representativeCalibration (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S Gamma : List Ty) (value : Nat) :
    ((NumberedUniformPackedDecoding.rawPackedDecode n arity Gamma value).map
      (ContextUniformPrimary.representative arity symbols S Gamma)).getD 0 =
      InternalQuotientEdgeChecker.targetRepresentativeValue n arity symbols S Gamma value := by
  rw [NumberedUniformPackedDecodingProof.rawPackedCalibration]
  cases hd : NumberedNumericDecoding.decodePackedNumber n arity Gamma value with
  | none => simp only [Option.map_none, Option.getD_none,
      InternalQuotientEdgeChecker.targetRepresentativeValue, hd]
  | some q =>
    simpa only [Option.map_some, Option.getD_some,
      InternalQuotientEdgeChecker.targetRepresentativeValue, hd] using
      ContextUniformPrimaryCalibrationProof.actualRawRepresentativeCalibration n arity symbols S Gamma q

theorem actualOriginalUniformLeafCalibration :
    InternalOriginalUniformParameterLeavesTargets.ActualOriginalUniformLeafCalibration := by
  intro n arity v
  unfold sourceValue targetValue representativeValue memberValue decodedValue
  cases hc : Encodable.decode (α := OrdinaryArithmeticQuotient.Context n)
      (Nat.unpair (v.get 1)).1 with
  | none => exact ⟨rfl,rfl,rfl,rfl⟩
  | some ctx =>
    cases ho : parameterObject (v.get 0) (v.get 1) with
    | none => exact ⟨rfl,rfl,rfl,rfl⟩
    | some obj =>
      exact ⟨rfl, targetCalibration n arity obj.1 obj.2,
        representativeCalibration n arity ctx.1.1 ctx.1.2 obj.1 obj.2, rfl⟩

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformParameterLeavesCalibrationProof

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformParameterLeavesCalibrationProof
