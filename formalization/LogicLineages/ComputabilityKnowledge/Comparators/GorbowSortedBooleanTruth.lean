module

public import LogicLineages.ComputabilityKnowledge.GorbowSortedBooleanTruth

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowSortedBooleanTruth
open GorbowSyntax GorbowSortedSyntaxCode GorbowSortedRevision GorbowBooleanTruth

def GuardCalibration : Prop := ∀ n (t : Term n) P ρ,
  (sentenceGuard t).realize (interpretation GorbowSortedRegistry.ground P) ρ ↔
    ∃ σ : Sentence,t.realize (interpretation GorbowSortedRegistry.ground P) ρ=formulaCode σ

def FunctionCalibration : Prop := ∀ n (s t : Term n) P ρ (σ τ : Sentence),
  s.realize (interpretation GorbowSortedRegistry.ground P) ρ=formulaCode σ →
  t.realize (interpretation GorbowSortedRegistry.ground P) ρ=formulaCode τ →
  (negCodeTerm s).realize (interpretation GorbowSortedRegistry.ground P) ρ=formulaCode (.neg σ) ∧
  (binaryCodeTerm 0 s t).realize (interpretation GorbowSortedRegistry.ground P) ρ=formulaCode (.imp σ τ) ∧
  (binaryCodeTerm 1 s t).realize (interpretation GorbowSortedRegistry.ground P) ρ=formulaCode (.conj σ τ) ∧
  (binaryCodeTerm 2 s t).realize (interpretation GorbowSortedRegistry.ground P) ρ=formulaCode (.disj σ τ)

def PositiveBooleanAxioms : Prop := ∀ initial k,
  negAxiom.realize (stage GorbowSortedRegistry.ground initial (k+1)) Fin.elim0 ∧
  impAxiom.realize (stage GorbowSortedRegistry.ground initial (k+1)) Fin.elim0 ∧
  conjAxiom.realize (stage GorbowSortedRegistry.ground initial (k+1)) Fin.elim0 ∧
  disjAxiom.realize (stage GorbowSortedRegistry.ground initial (k+1)) Fin.elim0

def Target : Prop := GuardCalibration ∧ FunctionCalibration ∧ PositiveBooleanAxioms
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowSortedBooleanTruth
