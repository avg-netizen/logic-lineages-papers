module

public import Init

@[expose] public section

/-!
# The full one-sorted arithmetic/knowledge/truth signature

This is syntax and standard-natural-number satisfaction for paper 12. It has
exactly arithmetic, U/u, Ag, unary and binary knowledge, and truth. Variables
use a finite de Bruijn context. An allowed one-variable selector is required
actually to contain its sole free variable.

No proof relation, self-indexed DCB presentation, arithmetized provability,
diagonal lemma, Löb theorem or KT consistency supplier is postulated here.
Those remain separate formalization obligations. In particular this module
does not identify the different 3.1.3 knowing-machine theory with Gorbow's KT.
-/

namespace LogicLineages.ComputabilityKnowledge.GorbowSyntax

inductive Term (n : Nat) where
  | var : Fin n → Term n
  | zero : Term n
  | succ : Term n → Term n
  | add : Term n → Term n → Term n
  | mul : Term n → Term n → Term n
  | universalFunction : Term n → Term n

inductive Formula : Nat → Type where
  | equal {n : Nat} : Term n → Term n → Formula n
  | universalRelation {n : Nat} : Term n → Formula n
  | agent {n : Nat} : Term n → Formula n
  | knowledgeAll {n : Nat} : Term n → Formula n
  | knowledge {n : Nat} : Term n → Term n → Formula n
  | truth {n : Nat} : Term n → Formula n
  | neg {n : Nat} : Formula n → Formula n
  | imp {n : Nat} : Formula n → Formula n → Formula n
  | conj {n : Nat} : Formula n → Formula n → Formula n
  | disj {n : Nat} : Formula n → Formula n → Formula n
  | all {n : Nat} : Formula (n + 1) → Formula n
  | ex {n : Nat} : Formula (n + 1) → Formula n

def Term.uses {n : Nat} (i : Fin n) : Term n → Bool
  | .var j => decide (i = j)
  | .zero => false
  | .succ t => t.uses i
  | .add t u => t.uses i || u.uses i
  | .mul t u => t.uses i || u.uses i
  | .universalFunction t => t.uses i

def Formula.uses : {n : Nat} → Fin n → Formula n → Bool
  | _, i, .equal t u => t.uses i || u.uses i
  | _, i, .universalRelation t => t.uses i
  | _, i, .agent t => t.uses i
  | _, i, .knowledgeAll t => t.uses i
  | _, i, .knowledge t u => t.uses i || u.uses i
  | _, i, .truth t => t.uses i
  | _, i, .neg φ => φ.uses i
  | _, i, .imp φ ψ => φ.uses i || ψ.uses i
  | _, i, .conj φ ψ => φ.uses i || ψ.uses i
  | _, i, .disj φ ψ => φ.uses i || ψ.uses i
  | _, i, .all φ => φ.uses i.succ
  | _, i, .ex φ => φ.uses i.succ

abbrev Sentence := Formula 0
abbrev Selector := {A : Formula 1 // A.uses 0 = true}

structure Interpretation where
  universalRelation : Nat → Prop
  universalFunction : Nat → Nat
  agents : Nat → Prop
  knowledgeAll : Nat → Prop
  knowledge : Nat → Nat → Prop
  truth : Nat → Prop

def Term.realize {n : Nat} (I : Interpretation) (v : Fin n → Nat) : Term n → Nat
  | .var i => v i
  | .zero => 0
  | .succ t => Nat.succ (t.realize I v)
  | .add t u => t.realize I v + u.realize I v
  | .mul t u => t.realize I v * u.realize I v
  | .universalFunction t => I.universalFunction (t.realize I v)

def Formula.realize (I : Interpretation) : {n : Nat} → (Fin n → Nat) → Formula n → Prop
  | _, v, .equal t u => t.realize I v = u.realize I v
  | _, v, .universalRelation t => I.universalRelation (t.realize I v)
  | _, v, .agent t => I.agents (t.realize I v)
  | _, v, .knowledgeAll t => I.knowledgeAll (t.realize I v)
  | _, v, .knowledge t u => I.knowledge (t.realize I v) (u.realize I v)
  | _, v, .truth t => I.truth (t.realize I v)
  | _, v, .neg φ => ¬ φ.realize I v
  | _, v, .imp φ ψ => φ.realize I v → ψ.realize I v
  | _, v, .conj φ ψ => φ.realize I v ∧ ψ.realize I v
  | _, v, .disj φ ψ => φ.realize I v ∨ ψ.realize I v
  | _, v, .all φ => ∀ x : Nat, φ.realize I (Fin.cases x v)
  | _, v, .ex φ => ∃ x : Nat, φ.realize I (Fin.cases x v)

def Term.numeral {n : Nat} : Nat → Term n
  | 0 => .zero
  | k + 1 => .succ (Term.numeral k)

theorem numeral_realize {n : Nat} (I : Interpretation) (v : Fin n → Nat) (k : Nat) :
    (Term.numeral k).realize I v = k := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg Nat.succ ih

def falseEquality : Sentence := .equal .zero (.succ .zero)

theorem falseEquality_not_realized (I : Interpretation) :
    ¬ falseEquality.realize I Fin.elim0 := by
  intro h
  change (0 : Nat) = Nat.succ 0 at h
  cases h

def everyone (A : Selector) (sentenceCode : Nat) : Sentence :=
  .all (.imp (.agent (.var 0))
    (.imp A.val (.knowledge (.var 0) (Term.numeral sentenceCode))))

def selectedNonempty (A : Selector) : Sentence :=
  .ex (.conj (.agent (.var 0)) A.val)

theorem everyone_realize (I : Interpretation) (A : Selector) (sentenceCode : Nat) :
    (everyone A sentenceCode).realize I Fin.elim0 ↔
      ∀ x : Nat, I.agents x → A.val.realize I (Fin.cases x Fin.elim0) →
        I.knowledge x sentenceCode := by
  change (∀ x : Nat, I.agents x → A.val.realize I (Fin.cases x Fin.elim0) →
    I.knowledge x ((Term.numeral sentenceCode).realize I (Fin.cases x Fin.elim0))) ↔ _
  constructor
  · intro h x hx ha
    have conclusion := h x hx ha
    rw [numeral_realize] at conclusion
    exact conclusion
  · intro h x hx ha
    rw [numeral_realize]
    exact h x hx ha

theorem selectedNonempty_realize (I : Interpretation) (A : Selector) :
    (selectedNonempty A).realize I Fin.elim0 ↔
      ∃ x : Nat, I.agents x ∧ A.val.realize I (Fin.cases x Fin.elim0) := Iff.rfl

end LogicLineages.ComputabilityKnowledge.GorbowSyntax
