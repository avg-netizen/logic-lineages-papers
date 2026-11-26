module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationGlobalTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationPathProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationEdgeGlobalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationGlobalProof

/-- Extend the existing globally calibrated tuple with the original
non-lambda and Object first-edge laws, keeping its complete earlier package. -/
theorem actualOriginalSourceNeutralApplicationGlobalSelection :
    OriginalSourceNeutralApplicationGlobalTargets.ActualOriginalSourceNeutralApplicationGlobalSelection := by
  intro n arity
  obtain ⟨p,hp,hr,hpackage,hroot,hmark,hbottom,hpaired,hquotient,happlication,hvariables⟩ :=
    OriginalNeutralApplicationEdgeGlobalProof.actualOriginalNeutralApplicationEdgeGlobalSelection n arity
  refine ⟨p,hp,hr,hpackage,hroot,hmark,hbottom,hpaired,hquotient,happlication,
    OriginalNonLambdaApplicationEdgeProof.actualOriginalNonLambdaApplicationEdgeElimination p,
    OriginalNonLambdaApplicationPathProof.actualOriginalNonLambdaApplicationPositivePathElimination p,?_⟩
  intro symbols S table hS
  exact ⟨OriginalSourceNeutralApplicationProof.actualOriginalSourceNeutralApplicationInputs
      n arity p hp symbols S table hS,
    OriginalSourceNeutralApplicationPathProof.actualOriginalSourceNeutralApplicationPositivePathElimination
      n arity p hp symbols S table hS,
    hvariables symbols S table hS⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationGlobalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationGlobalProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationGlobalProof.actualOriginalSourceNeutralApplicationGlobalSelection
