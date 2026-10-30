module

public import LogicLineages.ComputabilityKnowledge.GorbowSortedRevision
public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowRevisionSemantics

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowSortedRevision
open GorbowSyntax GorbowSortedSyntaxCode GorbowPACore
open LogicLineages.ComputabilityKnowledge.GorbowSortedRevision

def FixedInterpretation : Prop :=
  GorbowRevisionSemantics.SingletonCalibration ∧ GorbowRevisionSemantics.FixedMinus ∧ GorbowRevisionSemantics.ModelClauses

def ExactImage : Prop := ∀ g P,
  (∀ σ : Sentence, revise g P (formulaCode σ) ↔ σ.realize (interpretation g P) Fin.elim0) ∧
  (∀ code, revise g P code → ∃ σ : Sentence,code=formulaCode σ)

def TermExclusion : Prop := ∀ g P n (t : Term n), ¬ revise g P (termCode t)

def SuccessorCalibration : Prop := ∀ g initial n (σ : Sentence),
  ((truthSentence σ).realize (stage g initial (n+1)) Fin.elim0 ↔ σ.realize (stage g initial n) Fin.elim0) ∧
  ((allKnowledgeSentence σ).realize (stage g initial (n+1)) Fin.elim0 ↔ σ.realize (stage g initial n) Fin.elim0) ∧
  (∀ a, (knowledgeSentence a σ).realize (stage g initial (n+1)) Fin.elim0 ↔ a=0 ∧ σ.realize (stage g initial n) Fin.elim0)

def PositiveDistribution : Prop := ∀ g initial n (σ τ : Sentence),
  (stage g initial (n+1)).knowledgeAll (formulaCode (.imp σ τ)) →
  (stage g initial (n+1)).knowledgeAll (formulaCode σ) →
  (stage g initial (n+1)).knowledgeAll (formulaCode τ)

def CoreSoundness : Prop := ∀ g initial k n (φ : Formula n) (p : Proof φ) v,
  φ.realize (stage g initial k) v

def Target : Prop := FixedInterpretation ∧ ExactImage ∧ TermExclusion ∧ SuccessorCalibration ∧ PositiveDistribution ∧ CoreSoundness
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowSortedRevision
