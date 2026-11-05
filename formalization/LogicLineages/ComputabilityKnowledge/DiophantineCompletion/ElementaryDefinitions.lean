module
public import LogicLineages.ComputabilityKnowledge.DiophantinePolynomialBridge

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.DiophantineCompletion.Elementary

/-- Natural arithmetic, retaining zero inputs and zero constants. -/
inductive Expr (α : Type) where
  | constant : Nat → Expr α
  | variable : α → Expr α
  | add : Expr α → Expr α → Expr α
  | mul : Expr α → Expr α → Expr α
  deriving DecidableEq

def Expr.eval {α : Type} : Expr α → (α → Nat) → Nat
  | .constant c, _ => c
  | .variable i, ν => ν i
  | .add p q, ν => p.eval ν+q.eval ν
  | .mul p q, ν => p.eval ν*q.eval ν

def Expr.subterms {α : Type} [DecidableEq α] : Expr α → Finset (Expr α)
  | .constant c => {.constant c}
  | .variable i => {.variable i}
  | .add p q => insert (.add p q) (p.subterms ∪ q.subterms)
  | .mul p q => insert (.mul p q) (p.subterms ∪ q.subterms)

/-- Exactly the five elementary RHS forms in the source. Arithmetic operations
read existential wires, not arbitrary compound expressions. -/
inductive RHS (α β : Type) where
  | constant : Nat → RHS α β
  | variable : β → RHS α β
  | parameter : α → RHS α β
  | add : β → β → RHS α β
  | mul : β → β → RHS α β

def RHS.eval {α β : Type} (ν : α → Nat) (w : β → Nat) : RHS α β → Nat
  | .constant c => c
  | .variable i => w i
  | .parameter a => ν a
  | .add i j => w i+w j
  | .mul i j => w i*w j

structure Constraint (α β : Type) where
  output : β
  rhs : RHS α β

def Constraint.Holds {α β : Type} (c : Constraint α β) (ν : α → Nat) (w : β → Nat) : Prop :=
  w c.output=c.rhs.eval ν w

def RHS.rename {α β γ δ : Type} (f : α → γ) (g : β → δ) : RHS α β → RHS γ δ
  | .constant c => .constant c
  | .variable i => .variable (g i)
  | .parameter a => .parameter (f a)
  | .add i j => .add (g i) (g j)
  | .mul i j => .mul (g i) (g j)

def Constraint.rename {α β γ δ : Type} (f : α → γ) (g : β → δ)
    (c : Constraint α β) : Constraint γ δ := ⟨g c.output,c.rhs.rename f g⟩

/-- Move a finite block of original polynomial witnesses from parameters to
existential wires. The remaining original parameters retain their identity. -/
def RHS.moveParameters {α β γ : Type} : RHS (α ⊕ β) γ → RHS α (β ⊕ γ)
  | .constant c => .constant c
  | .variable i => .variable (.inr i)
  | .parameter (.inl a) => .parameter a
  | .parameter (.inr b) => .variable (.inl b)
  | .add i j => .add (.inr i) (.inr j)
  | .mul i j => .mul (.inr i) (.inr j)

def Constraint.moveParameters {α β γ : Type} (c : Constraint (α ⊕ β) γ) : Constraint α (β ⊕ γ) :=
  ⟨.inr c.output,c.rhs.moveParameters⟩

/-- A finite conjunction of elementary constraints, with finite natural
existential witnesses and exactly the original free parameter valuation. -/
def Represents {α : Type} (S : Set (α → Nat)) : Prop :=
  ∃ k m : Nat, ∃ C : Fin m → Constraint α (Fin k),
    ∀ ν, ν ∈ S ↔ ∃ w : Fin k → Nat, ∀ j : Fin m, (C j).Holds ν w

end LogicLineages.ComputabilityKnowledge.DiophantineCompletion.Elementary
