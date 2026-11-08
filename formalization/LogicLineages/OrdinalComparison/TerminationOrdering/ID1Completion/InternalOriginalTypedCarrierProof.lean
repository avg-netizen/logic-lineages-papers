module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalTypedCarrierEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalTypedCarrierSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalTypedCarrierProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalOriginalTypedCarrier InternalOriginalTypedCarrierSupportProof

 theorem actualOriginalTypedProgramExists :
    InternalOriginalTypedCarrierTargets.ActualOriginalTypedProgramExists :=
  InternalOriginalTypedCarrierEvaluationProof.actualOriginalTypedProgramExists

 theorem actualOriginalTypedWrapperCalibration :
    InternalOriginalTypedCarrierTargets.ActualOriginalTypedWrapperCalibration :=
  InternalOriginalTypedCarrierEvaluationProof.actualOriginalTypedWrapperCalibration

 theorem actualOriginalTypedAcceptanceEquation :
    InternalOriginalTypedCarrierTargets.ActualOriginalTypedAcceptanceEquation := by
  intro body validity oldTyped α value typ
  obtain ⟨hf⟩ := checkerRecover (body := body)
    (Gamma := [accepted validity oldTyped value typ]) validity oldTyped value typ
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := checkerAccept (body := body)
    (Gamma := [requirements validity oldTyped value typ]) validity oldTyped value typ
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalTypedCarrierProof
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalTypedCarrierProof
