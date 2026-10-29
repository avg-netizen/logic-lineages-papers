module

public import LogicLineages.ComputabilityKnowledge.GorbowSyntax

@[expose] public section

/-! Actual simultaneous substitution in the full source term language.
This supplies a syntactic dependency for later arithmetic coding; no formula
coding, representability or diagonal theorem is assumed or asserted here. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowSubstitution

open GorbowSyntax

def substitute {m n : Nat} (σ : Fin m → Term n) : Term m → Term n
  | .var i => σ i
  | .zero => .zero
  | .succ t => .succ (substitute σ t)
  | .add t u => .add (substitute σ t) (substitute σ u)
  | .mul t u => .mul (substitute σ t) (substitute σ u)
  | .universalFunction t => .universalFunction (substitute σ t)

theorem substitute_realize {m n : Nat} (I : Interpretation)
    (v : Fin n → Nat) (σ : Fin m → Term n) (t : Term m) :
    (substitute σ t).realize I v =
      t.realize I (fun i => (σ i).realize I v) := by
  induction t with
  | var i => rfl
  | zero => rfl
  | succ t ih => exact congrArg Nat.succ ih
  | add t u ht hu => simp only [substitute, Term.realize, ht, hu]
  | mul t u ht hu => simp only [substitute, Term.realize, ht, hu]
  | universalFunction t ih => exact congrArg I.universalFunction ih

theorem substitute_variables {n : Nat} (t : Term n) :
    substitute Term.var t = t := by
  induction t with
  | var i => rfl
  | zero => rfl
  | succ t ih => exact congrArg Term.succ ih
  | add t u ht hu => simp only [substitute, ht, hu]
  | mul t u ht hu => simp only [substitute, ht, hu]
  | universalFunction t ih => exact congrArg Term.universalFunction ih

theorem substitute_composition {l m n : Nat} (σ : Fin l → Term m)
    (τ : Fin m → Term n) (t : Term l) :
    substitute τ (substitute σ t) = substitute (fun i => substitute τ (σ i)) t := by
  induction t with
  | var i => rfl
  | zero => rfl
  | succ t ih => exact congrArg Term.succ ih
  | add t u ht hu => simp only [substitute, ht, hu]
  | mul t u ht hu => simp only [substitute, ht, hu]
  | universalFunction t ih => exact congrArg Term.universalFunction ih

end LogicLineages.ComputabilityKnowledge.GorbowSubstitution
