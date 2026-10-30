module

public import LogicLineages.ComputabilityKnowledge.GorbowSortedKnowledgeAxioms

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowSortedKnowledgeAxioms
open GorbowSyntax GorbowSortedRevision
open LogicLineages.ComputabilityKnowledge.GorbowSortedKnowledgeAxioms

def FixedClauses : Prop := ∀ (P : Extension),
  nontriviality.realize (interpretation GorbowSortedRegistry.ground P) Fin.elim0 ∧
  bridge.realize (interpretation GorbowSortedRegistry.ground P) Fin.elim0 ∧
  veracity.realize (interpretation GorbowSortedRegistry.ground P) Fin.elim0

def PositiveDistribution : Prop := ∀ initial k,
  distribution.realize (stage GorbowSortedRegistry.ground initial (k+1)) Fin.elim0

def InitialClosure : Prop := ∀ (P : Extension),
  (∀ (φ ψ : Sentence), P (GorbowSortedSyntaxCode.formulaCode φ) →
    P (GorbowSortedSyntaxCode.formulaCode (.imp φ ψ)) → P (GorbowSortedSyntaxCode.formulaCode ψ)) →
  distribution.realize (interpretation GorbowSortedRegistry.ground P) Fin.elim0

def Target : Prop := FixedClauses ∧ PositiveDistribution ∧ InitialClosure
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowSortedKnowledgeAxioms
