module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Definitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion
open GorbowSyntax

/-- Full-language selector, with the actual source's sorted contradiction
code. No knowledge/truth formula inside the selector is externally evaluated. -/
def selectorTheta (A : Selector) : Sentence :=
  .imp (everyone A (GorbowSortedSyntaxCode.formulaCode falseEquality)) falseEquality

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion
