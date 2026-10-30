module
public import LogicLineages.OrdinalComparison.HeadEndpointDefinitions

@[expose] public section

namespace LogicLineages.OrdinalComparison

/-- The source comparison key: first ordinal head, then total norm input. -/
def actualHeadKeyLess (lam : Ordinal.{0}) (t : Nat) (mu : Ordinal.{0}) (u : Nat) : Prop :=
  lam < mu ∨ lam = mu ∧ t < u

end LogicLineages.OrdinalComparison
