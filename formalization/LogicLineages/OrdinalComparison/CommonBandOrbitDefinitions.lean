module
public import LogicLineages.OrdinalComparison.PeakOrbitDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

/-- The two genuine source input regimes at a shared integer x. -/
def CommonBandOrRoot (x n : Nat) : Prop :=
  (x≤n ∧ n<Phi x) ∨ (ControlRoot n ∧ Phi x<n)

end LogicLineages.OrdinalComparison
