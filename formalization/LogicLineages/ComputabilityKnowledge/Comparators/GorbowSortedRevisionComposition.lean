module

public import LogicLineages.ComputabilityKnowledge.GorbowSortedRevisionComposition

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowSortedRevisionComposition
open GorbowSyntax GorbowFreeSupport GorbowNamedBinding GorbowFormulaComposition GorbowStandardInstances
open GorbowSortedSyntaxCode GorbowSortedRevision

def BooleanTruth : Prop := ∀ g initial k (σ τ : Sentence),
  ((truthSentence (.neg σ)).realize (stage g initial (k+1)) Fin.elim0 ↔ ¬ (truthSentence σ).realize (stage g initial (k+1)) Fin.elim0) ∧
  ((truthSentence (.imp σ τ)).realize (stage g initial (k+1)) Fin.elim0 ↔
    ((truthSentence σ).realize (stage g initial (k+1)) Fin.elim0 → (truthSentence τ).realize (stage g initial (k+1)) Fin.elim0)) ∧
  ((truthSentence (.conj σ τ)).realize (stage g initial (k+1)) Fin.elim0 ↔
    ((truthSentence σ).realize (stage g initial (k+1)) Fin.elim0 ∧ (truthSentence τ).realize (stage g initial (k+1)) Fin.elim0)) ∧
  ((truthSentence (.disj σ τ)).realize (stage g initial (k+1)) Fin.elim0 ↔
    ((truthSentence σ).realize (stage g initial (k+1)) Fin.elim0 ∨ (truthSentence τ).realize (stage g initial (k+1)) Fin.elim0))

def NamedQuantifiers : Prop := ∀ n (v : Fin n) (φ : Formula n), formulaSupport φ={v.val} →
  ∃ σ τ : Sentence, formulaCode σ=formulaCode (bindAll v φ) ∧ formulaCode τ=formulaCode (bindEx v φ) ∧
    ∀ g initial k,
      ((truthSentence σ).realize (stage g initial (k+1)) Fin.elim0 ↔
        ∀ t : Term 0, (truthSentence (namedClosedInstance v φ t)).realize (stage g initial (k+1)) Fin.elim0) ∧
      ((truthSentence τ).realize (stage g initial (k+1)) Fin.elim0 ↔
        ∃ t : Term 0, (truthSentence (namedClosedInstance v φ t)).realize (stage g initial (k+1)) Fin.elim0) ∧
      (∀ a, (stage g initial (k+1)).agents a →
        (∀ t : Term 0, ArithmeticTerm t →
          (knowledgeSentence a (namedClosedInstance v φ t)).realize (stage g initial (k+1)) Fin.elim0) →
        (knowledgeSentence a σ).realize (stage g initial (k+1)) Fin.elim0)

def Target : Prop := BooleanTruth ∧ NamedQuantifiers
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowSortedRevisionComposition
