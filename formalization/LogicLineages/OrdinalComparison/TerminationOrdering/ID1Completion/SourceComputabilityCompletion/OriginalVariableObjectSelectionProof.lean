module
public meta import LogicLineages.Audit
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableObjectSelectionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableObjectLeastProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableRepresentativeProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableObjectSelectionProof
open UniformCertificateCompletion

/-- The original globally selected tuple supplies all native contracts.
Both new internal laws apply to precisely its already selected refinement,
after the arbitrary source window is introduced. -/
theorem actualOriginalVariableObjectGlobalSelection :
    OriginalVariableObjectSelectionTargets.ActualOriginalVariableObjectGlobalSelection := by
  intro n arity
  obtain ⟨p,hp,_,_,hr,hpackage,_,_,_,_⟩ :=
    OriginalVariableRepresentativeProof.actualOriginalVariableRepresentativeGlobalSelection n arity
  refine ⟨p,hp,hr,hpackage,?_⟩
  intro symbols S table hS
  exact ⟨OriginalVariableObjectCertificateProof.actualOriginalVariableObjectCertificateBottom
      n arity p hp symbols S table hS,
    OriginalVariableObjectLeastProof.actualOriginalVariableObjectLeast
      n arity p hp symbols S table hS⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableObjectSelectionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableObjectSelectionProof
