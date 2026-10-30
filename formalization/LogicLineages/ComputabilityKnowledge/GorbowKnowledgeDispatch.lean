module

public import LogicLineages.ComputabilityKnowledge.GorbowRegistryDispatch
public import LogicLineages.ComputabilityKnowledge.GorbowAtomicRegistry
public import LogicLineages.ComputabilityKnowledge.GorbowSortedKnowledgeAxioms

@[expose] public section
/-! Actual knowledge clauses at a fixed registry and an explicit empty initial
extension. No represented Base or reflection axiom is included. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowKnowledgeDispatch
open GorbowSyntax GorbowSortedRevision GorbowSortedSyntaxCode

def emptyInitial : Extension := fun _ => False

def MPClosed (P : Extension) : Prop := ∀ φ ψ : Sentence,
  P (formulaCode φ) → P (formulaCode (.imp φ ψ)) → P (formulaCode ψ)
end LogicLineages.ComputabilityKnowledge.GorbowKnowledgeDispatch
