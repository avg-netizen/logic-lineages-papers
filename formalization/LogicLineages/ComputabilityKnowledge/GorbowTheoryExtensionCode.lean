module

public import LogicLineages.ComputabilityKnowledge.GorbowTheoryNumericCertificate
public import LogicLineages.ComputabilityKnowledge.GorbowClosedDeduction
public import LogicLineages.ComputabilityKnowledge.GorbowSortedBooleanCode

@[expose] public section
/-! Explicit external axiom-program extension by one raw sentence code.
Certificate existence is calibrated to implication by literal deduction;
this neither transforms certificates nor represents provability in PA. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowTheoryExtensionCode

def extendProgram (axCheck : List Nat → Bool) (r raw : List Nat) : Bool :=
  axCheck raw || decide (raw=r)
end LogicLineages.ComputabilityKnowledge.GorbowTheoryExtensionCode
