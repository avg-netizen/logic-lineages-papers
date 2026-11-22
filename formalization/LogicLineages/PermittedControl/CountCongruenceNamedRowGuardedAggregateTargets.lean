module
public import LogicLineages.PermittedControl.CountCongruenceNamedRowGuardedSemanticTargets

@[expose] public section
namespace LogicLineages.PermittedControl.CountCongruenceNamedRow

/-- Exact prepared row for one original signed count congruence. The semantic
clause compares the entire equivalence at assignments agreeing on name 1. -/
def FullGuardedCountCongruenceNamedRow : Prop :=
  CodeExact ∧ ShapeAndSupport ∧ ActualNamedRowGuarded

end LogicLineages.PermittedControl.CountCongruenceNamedRow
