module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOpeningSubstitutionTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOpeningSubstitutionProof
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction

theorem actualTermWeakeningSubstitution : NumberedOpeningSubstitutionTargets.ActualTermWeakeningSubstitution := by
  intro Symbol arity Gamma Delta theta sigma tau q
  rw [NumberedMixedBindingProof.substituteRename,NumberedMixedBindingProof.renameSubstitute]
  rfl

theorem actualArgumentWeakeningSubstitution : NumberedOpeningSubstitutionTargets.ActualArgumentWeakeningSubstitution := by
  intro Symbol arity Gamma Delta theta sigma types args
  rw [NumberedMixedBindingProof.actualArgumentSubstituteRename,
    NumberedMixedBindingProof.actualArgumentRenameSubstitute]
  rfl

theorem actualOpenNumberedSubstitution : NumberedOpeningSubstitutionTargets.ActualOpenNumberedSubstitution := by
  intro Symbol arity Gamma Delta theta label f sigma tau base extraTypes extras
  simp only [openNumbered,substitute]
  rw [actualArgumentWeakeningSubstitution,NumberedRewriteApplicationBindingProof.substituteAppend,
    actualArgumentWeakeningSubstitution]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOpeningSubstitutionProof
