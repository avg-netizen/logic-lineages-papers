module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralQuotientProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationComponentCoherenceGlobalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralQuotientGlobalProof

/-- Extend the existing once-selected tuple with the original quotient-edge
eliminator at that exact tuple. All prior package fields and laws are retained. -/
theorem actualOriginalNeutralQuotientGlobalSelection :
    OriginalNeutralQuotientTargets.ActualOriginalNeutralQuotientGlobalSelection := by
  intro n arity
  obtain ⟨p,hp,hr,hpackage,hroot,hmark,hbottom,hpaired,hvariables⟩ :=
    OriginalApplicationComponentCoherenceGlobalProof.actualOriginalApplicationComponentCoherenceGlobalSelection
      n arity
  exact ⟨p,hp,hr,hpackage,hroot,hmark,hbottom,hpaired,
    OriginalNeutralQuotientProof.actualOriginalNeutralQuotientEdgeElimination p,hvariables⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralQuotientGlobalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralQuotientGlobalProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralQuotientGlobalProof.actualOriginalNeutralQuotientGlobalSelection
