module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAnnotatedExpansionTypedTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAnnotatedExpansionTypedProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedLeastCodeRepresentative
open NumberedAuxiliaryCoding OriginalHereditaryAnnotatedExpansion
open OriginalHereditaryAnnotatedExpansionTypedTargets
open OriginalRawSyntaxTransport (arityValue tagValue)

theorem termChildren : TermChildren := by
  intro n arity Gamma q
  obtain ⟨tau,q⟩ := q
  cases q <;> simp [termAnnotations,arityValue,tagValue,termCode,codeNumber,
    annotationValue,typeNumber,Nat.unpair_pair,Nat.add_sub_cancel_left,
    List.range_succ,List.range_zero]

theorem argumentsChildren : ArgumentsChildren := by
  intro n arity Gamma types args
  cases args <;> simp [argumentAnnotations,arityValue,tagValue,argumentsCode,codeNumber,
    annotationValue,Nat.unpair_pair,List.range_succ,List.range_zero]

theorem deletionInheritance : DeletionInheritance := by
  intro k role typ raw h
  simp only [annotationValue,if_neg (Nat.not_lt.mpr h)]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAnnotatedExpansionTypedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAnnotatedExpansionTypedProof
