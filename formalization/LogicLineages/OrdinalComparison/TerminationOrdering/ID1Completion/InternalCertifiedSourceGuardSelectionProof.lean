module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCertifiedSourceGuardSelectionSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCertifiedSourceGuardSelectionEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCertifiedSourceGuardSelectionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open InternalCertifiedSourceGuardSelection InternalCertifiedSourceGuardSelectionSupportProof

theorem actualOriginalCertifiedSourceGuardCalibration :
    InternalCertifiedSourceGuardSelectionTargets.ActualOriginalCertifiedSourceGuardCalibration :=
  InternalCertifiedSourceGuardSelectionEvaluationProof.selectedCalibration

theorem actualOriginalCertifiedStepAcceptanceFactorization :
    InternalCertifiedSourceGuardSelectionTargets.ActualOriginalCertifiedStepAcceptanceFactorization := by
  intro data body α s t k
  obtain ⟨hf⟩ := stepRecover (body := body) (Gamma := [stepAccepted data s t k]) data s t k
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := stepAccept (body := body) (Gamma := [stepFactors data s t k]) data s t k
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

theorem actualOriginalCertifiedTypedAcceptanceFactorization :
    InternalCertifiedSourceGuardSelectionTargets.ActualOriginalCertifiedTypedAcceptanceFactorization := by
  intro data body α value typ
  obtain ⟨hf⟩ := typedRecover (body := body) (Gamma := [typedAccepted data value typ]) data value typ
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := typedAccept (body := body) (Gamma := [typedFactors data value typ]) data value typ
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

theorem actualOriginalCertifiedSourceGuardSelection :
    InternalCertifiedSourceGuardSelectionTargets.ActualOriginalCertifiedSourceGuardSelection := by
  intro n arity symbols S Gamma table hc
  obtain ⟨data,h⟩ := InternalCertifiedSourceGuardSelectionEvaluationProof.calibratedDataExists
    n arity symbols S Gamma table
  exact ⟨data,h,actualOriginalCertifiedSourceGuardCalibration
    n arity symbols S Gamma table data hc h,
    fun body α => ⟨fun s t k => actualOriginalCertifiedStepAcceptanceFactorization data body α s t k,
      fun value typ => actualOriginalCertifiedTypedAcceptanceFactorization data body α value typ⟩⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCertifiedSourceGuardSelectionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCertifiedSourceGuardSelectionProof
