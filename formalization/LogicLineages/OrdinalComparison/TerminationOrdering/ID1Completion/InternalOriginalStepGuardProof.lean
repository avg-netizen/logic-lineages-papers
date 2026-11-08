module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalStepGuardEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalStepGuardSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalStepGuardProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalOriginalStepGuard InternalOriginalStepGuardSupportProof InternalApplicationCertificateConstructorsProof

 theorem actualOriginalValidityProgramsExist :
    InternalOriginalStepGuardTargets.ActualOriginalValidityProgramsExist :=
  InternalOriginalStepGuardEvaluationProof.actualOriginalValidityProgramsExist

 theorem actualOriginalGuardedStepCalibration :
    InternalOriginalStepGuardTargets.ActualOriginalGuardedStepCalibration :=
  InternalOriginalStepGuardEvaluationProof.actualOriginalGuardedStepCalibration

 theorem actualOriginalAcceptanceAtTags :
    InternalOriginalStepGuardTargets.ActualOriginalAcceptanceAtTags := by
  intro body data oldChecker α sourceTag targetTag s t k
  apply guardedIff
  · exact checkerRecover data oldChecker sourceTag targetTag s t k
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩
  · exact checkerAccept data oldChecker sourceTag targetTag s t k
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩

 theorem actualOriginalTaggedAcceptance :
    InternalOriginalStepGuardTargets.ActualOriginalTaggedAcceptance := by
  intro body data oldChecker α tag s t k
  apply guardedIff
  · exact taggedRecover data oldChecker tag s t k
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩
  · exact taggedAccept data oldChecker tag s t k
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalStepGuardProof
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalStepGuardProof
