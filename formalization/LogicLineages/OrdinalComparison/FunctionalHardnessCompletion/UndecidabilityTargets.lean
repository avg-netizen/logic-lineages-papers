module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.UndecidabilityDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.UndecidabilityTargets

/-- The exact cited finite-system undecidability supplier, on explicit natural
codes. This is a pending target, not an axiom, premise or theorem instance. A
proof must supply the actual Narendran/H10 dependency chain. -/
def PolynomialSystemUndecidable : Prop := ¬ ComputablePred encodedPolynomialSolvable

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.UndecidabilityTargets
