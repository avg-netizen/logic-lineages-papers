module

public import LogicLineages.ComputabilityKnowledge.GorbowBooleanTruth

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowBooleanTruth
open GorbowSyntax GorbowCodeConstructors GorbowRevisionSemantics
open LogicLineages.ComputabilityKnowledge.GorbowBooleanTruth

def GuardCalibration : Prop := ∀ n (t : Term n) P ρ,
  (sentenceGuard t).realize (interpretation GorbowBooleanRegistry.ground P) ρ ↔
    ∃ σ : Sentence, t.realize (interpretation GorbowBooleanRegistry.ground P) ρ=formulaNumber σ

def FunctionCalibration : Prop := ∀ n (s t : Term n) P ρ (σ τ : Sentence),
  s.realize (interpretation GorbowBooleanRegistry.ground P) ρ=formulaNumber σ →
  t.realize (interpretation GorbowBooleanRegistry.ground P) ρ=formulaNumber τ →
  (negCodeTerm s).realize (interpretation GorbowBooleanRegistry.ground P) ρ=formulaNumber (.neg σ) ∧
  (binaryCodeTerm 0 s t).realize (interpretation GorbowBooleanRegistry.ground P) ρ=formulaNumber (.imp σ τ) ∧
  (binaryCodeTerm 1 s t).realize (interpretation GorbowBooleanRegistry.ground P) ρ=formulaNumber (.conj σ τ) ∧
  (binaryCodeTerm 2 s t).realize (interpretation GorbowBooleanRegistry.ground P) ρ=formulaNumber (.disj σ τ)

def PositiveBooleanAxioms : Prop := ∀ initial k,
  negAxiom.realize (stage GorbowBooleanRegistry.ground initial (k+1)) Fin.elim0 ∧
  impAxiom.realize (stage GorbowBooleanRegistry.ground initial (k+1)) Fin.elim0 ∧
  conjAxiom.realize (stage GorbowBooleanRegistry.ground initial (k+1)) Fin.elim0 ∧
  disjAxiom.realize (stage GorbowBooleanRegistry.ground initial (k+1)) Fin.elim0

def Target : Prop := GuardCalibration ∧ FunctionCalibration ∧ PositiveBooleanAxioms
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowBooleanTruth
