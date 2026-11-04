module
public import LogicLineages.OrdinalComparison.ParametricFinitePairCollapseDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricFiniteCoefficient
/-- Input-dependent finite iteration, not a worklist fuel or runtime bound. -/
def formula (G : Nat → Nat) (p : Nat × Nat) : Nat := (G^[p.1]) (2*p.1+p.2)+p.1
def maximizer (G : Nat → Nat) (a b : Nat) : Nat × Nat :=
  (a,G (2*(a+1)+b)-2*a)
end LogicLineages.OrdinalComparison.Source.ParametricFiniteCoefficient
