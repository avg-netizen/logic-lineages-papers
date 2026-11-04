module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedArgumentSubstitutionTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedArgumentSubstitutionProof
open Source Source.SourceMarkedSyntax Source.SourceSpecialApplication NumberedRewriteSyntax NumberedRewriteReduction

theorem actualApplyArgumentsSubstitution : NumberedArgumentSubstitutionTargets.ActualApplyArgumentsSubstitution := by
  intro Symbol arity Gamma Delta theta types
  induction types with
  | nil => intro tau q args; cases args; rfl
  | cons sigma types ih =>
    intro tau q args
    cases args with
    | cons a rest => exact ih tau (.app q a) rest

theorem actualSelfArgumentsSubstitution : NumberedArgumentSubstitutionTargets.ActualSelfArgumentsSubstitution := by
  intro Symbol arity Gamma Delta theta label f base extraTypes extras types
  induction types with
  | nil => rfl
  | cons tau types ih =>
    exact congrArg (AuxArguments.cons (.numbered label f tau
      (substituteArguments base theta) extraTypes (substituteArguments extras theta))) ih

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedArgumentSubstitutionProof
