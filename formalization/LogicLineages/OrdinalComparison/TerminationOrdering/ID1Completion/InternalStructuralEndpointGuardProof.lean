module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStructuralEndpointGuardEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStructuralEndpointGuardSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStructuralEndpointGuardProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalStructuralEndpointGuard InternalStructuralEndpointGuardSupportProof
open InternalApplicationCertificateConstructorsProof

 theorem actualOriginalMembershipProgramExists :
    InternalStructuralEndpointGuardTargets.ActualOriginalMembershipProgramExists :=
  InternalStructuralEndpointGuardEvaluationProof.actualOriginalMembershipProgramExists

 theorem actualOriginalStructuralEndpointCalibration :
    InternalStructuralEndpointGuardTargets.ActualOriginalStructuralEndpointCalibration :=
  InternalStructuralEndpointGuardEvaluationProof.actualOriginalStructuralEndpointCalibration

 theorem actualOriginalEndpointAcceptanceAtArrow :
    InternalStructuralEndpointGuardTargets.ActualOriginalEndpointAcceptanceAtArrow := by
  intro body validity member α arrow d e s t a
  apply guardedIff
  · exact endpointRecover validity member arrow d e s t a
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩
  · exact endpointAccept validity member arrow d e s t a
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStructuralEndpointGuardProof
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStructuralEndpointGuardProof
