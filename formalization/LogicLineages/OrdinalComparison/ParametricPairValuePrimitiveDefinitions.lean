module
public import LogicLineages.OrdinalComparison.ParametricFiniteCoefficientDefinitions
public import LogicLineages.OrdinalComparison.ParametricPairCollapseComputableDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricPairValuePrimitive
def iterateValue (H : Nat × Nat → Nat) (p : Nat × (Nat × Nat)) : Nat :=
  ((fun n => H (p.1,n))^[p.2.1]) (2*p.2.1+p.2.2)+p.2.1
end LogicLineages.OrdinalComparison.Source.ParametricPairValuePrimitive
