module

public import LogicLineages.ComputabilityKnowledge.GorbowPRNumeralCalculationDefinitions

@[expose] public section
/-! Simultaneous substitution into the unchanged full-language syntax, now
retaining an arbitrary output context. Unlike numeral calculation, arguments
may contain free certificate/fuel variables. No new proof constructor, source
Base identification or external-evaluation-to-internal-proof rule is added. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowPRSymbolicEquations
open GorbowSyntax

def symbolicInstance {n ctx : Nat} (phi : Formula n) (sigma : Fin n → Term ctx) : Formula ctx :=
  GorbowFormulaSubstitution.substituteFormula sigma phi

end LogicLineages.ComputabilityKnowledge.GorbowPRSymbolicEquations
