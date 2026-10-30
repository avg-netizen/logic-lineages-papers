module

public import LogicLineages.ComputabilityKnowledge.GorbowRevisionEventual

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowRevisionEventual
open GorbowSyntax GorbowPACore GorbowRevisionSemantics
open LogicLineages.ComputabilityKnowledge.GorbowRevisionEventual

def KnowledgeCalibration : Prop := ∀ g initial n (σ : Sentence),
  ((allAgentsKnow σ).realize (stage g initial n) Fin.elim0 ↔
    (allKnowledgeSentence σ).realize (stage g initial n) Fin.elim0) ∧
  ((allAgentsKnow σ).realize (stage g initial (n+1)) Fin.elim0 ↔
    σ.realize (stage g initial n) Fin.elim0)

def RuleThresholds : Prop := ∀ g initial (σ : Sentence) N,
  (Threshold g initial σ N → Threshold g initial (truthSentence σ) (N+1)) ∧
  (Threshold g initial (truthSentence σ) N → Threshold g initial σ N) ∧
  (Threshold g initial σ N → Threshold g initial (allAgentsKnow σ) (N+1))

def ModusPonens : Prop := ∀ g initial (σ τ : Sentence) N M,
  Threshold g initial (.imp σ τ) N → Threshold g initial σ M → Threshold g initial τ (max N M)

def FiniteThreshold : Prop := ∀ g initial (sentences : List Sentence),
  (∀ σ ∈ sentences, Eventually g initial σ) → ∃ N, ∀ σ ∈ sentences, Threshold g initial σ N

def CoreThreshold : Prop := ∀ g initial (σ : Sentence) (p : Proof σ), Threshold g initial σ 0

def NeverContradiction : Prop := ∀ g initial, ¬ Eventually g initial falseEquality

def EventualRules : Prop := ∀ g initial (σ : Sentence),
  (Eventually g initial σ → Eventually g initial (truthSentence σ)) ∧
  (Eventually g initial (truthSentence σ) → Eventually g initial σ) ∧
  (Eventually g initial σ → Eventually g initial (allAgentsKnow σ))

def Target : Prop := KnowledgeCalibration ∧ RuleThresholds ∧ ModusPonens ∧ FiniteThreshold ∧
  CoreThreshold ∧ NeverContradiction ∧ EventualRules
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowRevisionEventual
