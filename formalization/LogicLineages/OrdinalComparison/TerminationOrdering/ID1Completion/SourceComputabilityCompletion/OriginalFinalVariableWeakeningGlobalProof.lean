module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableWeakeningProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableLeavesGlobalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableWeakeningGlobalProof
open OriginalFinalVariableWeakening OriginalFinalVariableWeakeningProof

/-- One selected input retains the WHOLE previous variable/native-accessibility
package and both independent laws at its SAME constructed finalData pipeline. -/
theorem actualOriginalFinalVariableWeakeningSelection :
    OriginalFinalVariableWeakeningTargets.ActualOriginalFinalVariableWeakeningSelection := by
  intro n arity
  obtain ⟨p,guard,hp,hg,hq,hproperties,hbranches,hequality⟩ :=
    OriginalVariableLeavesGlobalProof.actualOriginalVariableLeavesGlobalSelection n arity
  exact ⟨p,guard,hp,hg,hq,hproperties,hbranches,hequality,
    actualOriginalFinalVariableSourceWeakening guard p,
    actualOriginalFinalVariableTargetWeakening guard p⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableWeakeningGlobalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableWeakeningGlobalProof
