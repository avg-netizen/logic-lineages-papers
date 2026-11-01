module
public import LogicLineages.OrdinalComparison.OneVariableComparisonDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

/-- The actual source range-expression domain, plus an explicit affine-growth
bound. No source value is evaluated while this tail is computed. -/
def encodedRangeAffineTail (source a b : Nat) : Nat :=
  max (encodedOneVariableComparisonDomainBound source) (max 4 (a+b+3))

end LogicLineages.OrdinalComparison
