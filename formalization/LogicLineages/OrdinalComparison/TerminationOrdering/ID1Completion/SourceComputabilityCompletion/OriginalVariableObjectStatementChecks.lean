module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableObjectSelectionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableObjectStatementChecks

/-- Exact inherited Object-certificate target, with unchanged antecedent. -/
theorem certificateBottom_exact :
    OriginalVariableObjectTargets.ActualOriginalVariableObjectCertificateBottom :=
  OriginalVariableObjectCertificateProof.actualOriginalVariableObjectCertificateBottom

/-- Exact inherited arbitrary-finite-type scalar leastness target. -/
theorem variableLeast_exact :
    OriginalVariableObjectTargets.ActualOriginalVariableObjectLeast :=
  OriginalVariableObjectLeastProof.actualOriginalVariableObjectLeast

/-- One original global source retains the package and both new laws. -/
theorem globalSelection_exact :
    OriginalVariableObjectSelectionTargets.ActualOriginalVariableObjectGlobalSelection :=
  OriginalVariableObjectSelectionProof.actualOriginalVariableObjectGlobalSelection

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableObjectStatementChecks

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableObjectStatementChecks
