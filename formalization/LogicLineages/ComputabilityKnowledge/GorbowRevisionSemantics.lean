module

public import LogicLineages.ComputabilityKnowledge.GorbowCodeConstructors
public import LogicLineages.ComputabilityKnowledge.GorbowPACore

@[expose] public section

/-! The manuscript's one-world, one-agent standard-N revision construction.
The sole world is Unit, accessibility is reflexive/total on that singleton,
and the sole agent is 0. U/u are arbitrary fixed interpretations, not a
postulated representation of Base or the self-referential DCB presentation.
Revision is external classical satisfaction, with no computability claim. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowRevisionSemantics
open GorbowSyntax GorbowCodeConstructors

structure Ground where
  universalRelation : Nat → Prop
  universalFunction : Nat → Nat

abbrev Extension := Nat → Prop

def interpretation (g : Ground) (P : Extension) : Interpretation where
  universalRelation := g.universalRelation
  universalFunction := g.universalFunction
  agents := fun a => a=0
  knowledgeAll := P
  knowledge := fun a c => a=0 ∧ P c
  truth := P

def singletonAccessible (_ _ : Unit) : Prop := True
def singletonKnowledge (P : Extension) (a c : Nat) : Prop :=
  a=0 ∧ ∀ w : Unit, singletonAccessible () w → P c

def MinusFormula : {n : Nat} → Formula n → Prop
  | _, .equal _ _ => True
  | _, .universalRelation _ => True
  | _, .agent _ => True
  | _, .knowledgeAll _ => False
  | _, .knowledge _ _ => False
  | _, .truth _ => False
  | _, .neg a => MinusFormula a
  | _, .imp a b => MinusFormula a ∧ MinusFormula b
  | _, .conj a b => MinusFormula a ∧ MinusFormula b
  | _, .disj a b => MinusFormula a ∧ MinusFormula b
  | _, .all a => MinusFormula a
  | _, .ex a => MinusFormula a

def revise (g : Ground) (P : Extension) : Extension :=
  fun c => ∃ σ : Sentence, formulaNumber σ = c ∧ σ.realize (interpretation g P) Fin.elim0

def extensions (g : Ground) (initial : Extension) : Nat → Extension
  | 0 => initial
  | n+1 => revise g (extensions g initial n)
def stage (g : Ground) (initial : Extension) (n : Nat) : Interpretation :=
  interpretation g (extensions g initial n)

def truthSentence (σ : Sentence) : Sentence := .truth (Term.numeral (formulaNumber σ))
def knowledgeSentence (a : Nat) (σ : Sentence) : Sentence :=
  .knowledge (Term.numeral a) (Term.numeral (formulaNumber σ))
def allKnowledgeSentence (σ : Sentence) : Sentence := .knowledgeAll (Term.numeral (formulaNumber σ))
end LogicLineages.ComputabilityKnowledge.GorbowRevisionSemantics
