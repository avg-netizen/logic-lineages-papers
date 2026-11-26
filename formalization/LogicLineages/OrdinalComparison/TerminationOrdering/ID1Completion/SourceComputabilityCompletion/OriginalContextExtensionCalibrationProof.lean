module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextExtensionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextExtensionCalibrationProof
open Source NumberedLeastCodeRepresentative
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The actual Ty instance was built from this original numeric equivalence. -/
theorem typeEncoding (sigma : Ty) : Encodable.encode sigma = typeNumber sigma := rfl

theorem contextEncoding (sigma : Ty) (Gamma : List Ty) :
    Encodable.encode (sigma :: Gamma) =
      Nat.succ (Nat.pair (typeNumber sigma) (Encodable.encode Gamma)) := by
  rw [Encodable.encode_list_cons,typeEncoding]

theorem objectEncoding (Gamma : List Ty) (raw : Nat) :
    ContextUniform.objectCode Gamma raw = Nat.pair (Encodable.encode Gamma) raw := by
  rw [ContextUniform.objectCode,Encodable.encode_prod_val,Encodable.encode_nat]

theorem actualOriginalContextEncodingCalibration :
    OriginalContextExtensionTargets.ActualOriginalContextEncodingCalibration :=
  ⟨typeEncoding,contextEncoding,objectEncoding⟩

/-- Standard-model calibration only. No internal derivation is inferred here. -/
theorem actualOriginalContextConsCalibration :
    OriginalContextExtensionTargets.ActualOriginalContextConsCalibration := by
  intro sigma Gamma
  simp only [InternalEqualityTestEvaluationProof.vectorTwo,
    Matrix.cons_val_zero,Matrix.cons_val_one,InternalListCodecEvaluationProof.consEvaluation,
    contextEncoding,Nat.add_comm 1,Nat.succ_eq_add_one]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextExtensionCalibrationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextExtensionCalibrationProof
