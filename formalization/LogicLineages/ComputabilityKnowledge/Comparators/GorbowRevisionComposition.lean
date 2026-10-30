module

public import LogicLineages.ComputabilityKnowledge.GorbowRevisionComposition

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowRevisionComposition
open GorbowSyntax GorbowCodeConstructors GorbowStandardInstances GorbowRevisionSemantics
open LogicLineages.ComputabilityKnowledge.GorbowRevisionComposition

def BooleanTruth : Prop := ∀ g initial n (σ τ : Sentence),
  ((truthSentence (.neg σ)).realize (stage g initial (n+1)) Fin.elim0 ↔
    ¬ (truthSentence σ).realize (stage g initial (n+1)) Fin.elim0) ∧
  ((truthSentence (.imp σ τ)).realize (stage g initial (n+1)) Fin.elim0 ↔
    ((truthSentence σ).realize (stage g initial (n+1)) Fin.elim0 → (truthSentence τ).realize (stage g initial (n+1)) Fin.elim0)) ∧
  ((truthSentence (.conj σ τ)).realize (stage g initial (n+1)) Fin.elim0 ↔
    ((truthSentence σ).realize (stage g initial (n+1)) Fin.elim0 ∧ (truthSentence τ).realize (stage g initial (n+1)) Fin.elim0)) ∧
  ((truthSentence (.disj σ τ)).realize (stage g initial (n+1)) Fin.elim0 ↔
    ((truthSentence σ).realize (stage g initial (n+1)) Fin.elim0 ∨ (truthSentence τ).realize (stage g initial (n+1)) Fin.elim0))

def FullTermQuantifiers : Prop := ∀ g initial n (A : Selector),
  ((truthSentence (.all A.val)).realize (stage g initial (n+1)) Fin.elim0 ↔
    ∀ t : Term 0, (truthSentence (instantiate A.val t)).realize (stage g initial (n+1)) Fin.elim0) ∧
  ((truthSentence (.ex A.val)).realize (stage g initial (n+1)) Fin.elim0 ↔
    ∃ t : Term 0, (truthSentence (instantiate A.val t)).realize (stage g initial (n+1)) Fin.elim0)

def AtomicTruth : Prop := ∀ g initial n k (R : Formula k), AtomicMinus R → AllContextVariables R →
  ∀ σ : Fin k → Term 0, (∀ i, ArithmeticTerm (σ i)) →
  ((truthSentence (GorbowFormulaSubstitution.substituteFormula σ R)).realize (stage g initial (n+1)) Fin.elim0 ↔
    R.realize (stage g initial (n+1)) (fun i => (σ i).realize (stage g initial (n+1)) Fin.elim0))

def ArithmeticBarcan : Prop := ∀ g initial n (A : Selector) a,
  (stage g initial (n+1)).agents a →
  (∀ t : Term 0, ArithmeticTerm t →
    (knowledgeSentence a (instantiate A.val t)).realize (stage g initial (n+1)) Fin.elim0) →
  (knowledgeSentence a (.all A.val)).realize (stage g initial (n+1)) Fin.elim0

def Target : Prop := BooleanTruth ∧ FullTermQuantifiers ∧ AtomicTruth ∧ ArithmeticBarcan
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowRevisionComposition
