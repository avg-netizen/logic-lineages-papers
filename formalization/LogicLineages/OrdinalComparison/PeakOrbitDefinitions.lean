module
public import LogicLineages.OrdinalComparison.ActualTerminalDefinitions

@[expose] public section

namespace LogicLineages.OrdinalComparison

/-- Paper07's exact notion: a root is outside the range of the fixed control. -/
def ControlRoot (n : Nat) : Prop := n ∉ Set.range Phi

end LogicLineages.OrdinalComparison
