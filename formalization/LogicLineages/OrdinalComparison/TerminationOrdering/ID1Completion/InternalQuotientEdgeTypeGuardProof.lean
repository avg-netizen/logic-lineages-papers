module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientEdgeTypeGuardEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientEdgeTypeGuardSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientEdgeTypeGuardProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalQuotientEdgeTypeGuard InternalQuotientEdgeTypeGuardSupportProof
open InternalApplicationCertificateConstructorsProof InternalApplicationStepPeelSupportProof

theorem actualOriginalQuotientEdgeTypedEndpoints :
    InternalQuotientEdgeTypeGuardTargets.ActualOriginalQuotientEdgeTypedEndpoints :=
  InternalQuotientEdgeTypeGuardEvaluationProof.actualOriginalQuotientEdgeTypedEndpoints

theorem actualOriginalQuotientEdgeTypedWrapperCalibration :
    InternalQuotientEdgeTypeGuardTargets.ActualOriginalQuotientEdgeTypedWrapperCalibration :=
  InternalQuotientEdgeTypeGuardEvaluationProof.actualOriginalQuotientEdgeTypedWrapperCalibration

theorem actualOriginalQuotientEdgeTypedAcceptanceEquation :
    InternalQuotientEdgeTypeGuardTargets.ActualOriginalQuotientEdgeTypedAcceptanceEquation := by
  intro body data typedProgram α x y certificate typ
  apply guardedIff
  · exact checkerRecover data typedProgram x y certificate typ
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩
  · exact checkerAccept data typedProgram x y certificate typ
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩

theorem actualOriginalQuotientEdgeTypedTransport :
    InternalQuotientEdgeTypeGuardTargets.ActualOriginalQuotientEdgeTypedTransport := by
  intro body data typedProgram α x y certificate typ
  obtain ⟨h⟩ := checkerRecover (body := body)
    (Gamma := [sourceTypeGraph typ x,accepted data typedProgram x y certificate])
    data typedProgram x y certificate typ
    ⟨Derivation.hypothesis List.mem_cons_self⟩
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction
    (Derivation.conjunctionRight h))⟩

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientEdgeTypeGuardProof
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientEdgeTypeGuardProof
