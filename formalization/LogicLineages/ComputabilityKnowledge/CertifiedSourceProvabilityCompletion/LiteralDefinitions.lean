module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Definitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion
open GorbowSyntax

/-- The literal displayed theta in source eq:counterexample. Its universal
antecedent has Ag(x) -> K(x,#b), without the extra top-selector x=x guard.
It is not identified syntactically with the passed sourceTheta helper. -/
def literalTheta : Sentence :=
  .imp (GorbowSortedRevisionEventual.allAgentsKnow falseEquality) falseEquality

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion
