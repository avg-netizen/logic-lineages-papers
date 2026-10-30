module

public import LogicLineages.ComputabilityKnowledge.GorbowClosedEquality

@[expose] public section
/-! Closed arithmetic calculation as actual PA-core proof syntax. The target
is restricted to arithmetic terms and does not turn arbitrary semantic truth
into derivability. No uniform graph representation is asserted. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowArithmeticDerivation
open GorbowSyntax

def Calculation (t : Term 0) (n : Nat) : Prop :=
  Nonempty (GorbowPACore.Proof (.equal t (Term.numeral n)))
end LogicLineages.ComputabilityKnowledge.GorbowArithmeticDerivation
