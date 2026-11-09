module

public import LogicLineages.ComputabilityKnowledge.GorbowPublishedKTDefinitions

@[expose] public section
/-! Exact original selected-agent syntax for the direct finite-iteration
route. The iteration length is an external natural number; no internal
uniform iteration, common-knowledge identification, or HB axiom is added. -/
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion
open GorbowSyntax

def topSelector : Selector :=
  ⟨.equal (.var 0) (.var 0), by decide⟩

def selectedIteration (A : Selector) : Nat → Sentence → Sentence
  | 0, sigma => sigma
  | r + 1, sigma => everyone A
      (GorbowSortedSyntaxCode.formulaCode (selectedIteration A r sigma))

/-- The current actual source uses the sorted formula code. The legacy
GorbowSelectedCode.theta uses an older unsorted code and is not reused. -/
def sourceTheta : Sentence :=
  .imp (everyone topSelector (GorbowSortedSyntaxCode.formulaCode falseEquality)) falseEquality

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion
