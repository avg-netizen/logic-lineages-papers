module

public import LogicLineages.ComputabilityKnowledge.GorbowRevisionSemantics

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowRevisionSemantics
open GorbowSyntax GorbowCodeConstructors GorbowPACore
open LogicLineages.ComputabilityKnowledge.GorbowRevisionSemantics

def SingletonCalibration : Prop := ∀ g P,
  (∀ a c, (interpretation g P).knowledge a c ↔ singletonKnowledge P a c) ∧
  (∀ c, (interpretation g P).knowledgeAll c ↔ ∀ a, a=0 → singletonKnowledge P a c) ∧
  (∀ w : Unit, singletonAccessible w w)

def FixedMinus : Prop := ∀ (g : Ground) (P Q : Extension),
  (∀ n (t : Term n) v, t.realize (interpretation g P) v = t.realize (interpretation g Q) v) ∧
  (∀ n (φ : Formula n) v, MinusFormula φ →
    (φ.realize (interpretation g P) v ↔ φ.realize (interpretation g Q) v))

def ExactImage : Prop := ∀ g P,
  (∀ σ : Sentence, revise g P (formulaNumber σ) ↔ σ.realize (interpretation g P) Fin.elim0) ∧
  (∀ c, (¬ ∃ σ : Sentence, formulaNumber σ=c) → ¬ revise g P c)

def SuccessorCalibration : Prop := ∀ g initial n (σ : Sentence),
  ((truthSentence σ).realize (stage g initial (n+1)) Fin.elim0 ↔ σ.realize (stage g initial n) Fin.elim0) ∧
  ((allKnowledgeSentence σ).realize (stage g initial (n+1)) Fin.elim0 ↔ σ.realize (stage g initial n) Fin.elim0) ∧
  (∀ a, (knowledgeSentence a σ).realize (stage g initial (n+1)) Fin.elim0 ↔
    a=0 ∧ σ.realize (stage g initial n) Fin.elim0)

def ModelClauses : Prop := ∀ g P,
  (∃ a, (interpretation g P).agents a) ∧
  (∀ c, (interpretation g P).knowledgeAll c ↔ ∀ a, (interpretation g P).agents a → (interpretation g P).knowledge a c) ∧
  (∀ a c, (interpretation g P).agents a → (interpretation g P).knowledge a c → (interpretation g P).truth c)

def PositiveDistribution : Prop := ∀ g initial n (σ τ : Sentence),
  (stage g initial (n+1)).knowledgeAll (formulaNumber (.imp σ τ)) →
  (stage g initial (n+1)).knowledgeAll (formulaNumber σ) →
  (stage g initial (n+1)).knowledgeAll (formulaNumber τ)

def CoreSoundness : Prop := ∀ g initial k n (φ : Formula n) (p : Proof φ) v,
  φ.realize (stage g initial k) v

def Target : Prop := SingletonCalibration ∧ FixedMinus ∧ ExactImage ∧ SuccessorCalibration ∧
  ModelClauses ∧ PositiveDistribution ∧ CoreSoundness
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowRevisionSemantics
