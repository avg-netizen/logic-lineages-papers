module

public import LogicLineages.ComputabilityKnowledge.GorbowPAAdditiveStructureDefinitions

@[expose] public section
/-! Quantified arithmetic formulas needed for the literal ordinary-arithmetic
beta trace. These remain formulas of the existing full-language PA calculus,
not additional axioms or standard-model validity assumptions. -/
namespace LogicLineages.ComputabilityKnowledge.SourceBaseCompletion.AdditionLaws
open GorbowSyntax

/-- Bound context [z,y,x]; all three variables range over the full domain. -/
def associativity : Sentence := .all (.all (.all
  (.equal (.add (.add (.var 2) (.var 1)) (.var 0))
    (.add (.var 2) (.add (.var 1) (.var 0))))))

/-- Bound context [y,x]. -/
def commutativity : Sentence := .all (.all
  (.equal (.add (.var 1) (.var 0)) (.add (.var 0) (.var 1))))

/-- Bound context [y,x]; no bounded-domain or nonnegativity premise is added. -/
def leftZeroOfSumZero : Sentence := .all (.all
  (.imp (.equal (.add (.var 1) (.var 0)) .zero)
    (.equal (.var 1) .zero)))

end LogicLineages.ComputabilityKnowledge.SourceBaseCompletion.AdditionLaws
