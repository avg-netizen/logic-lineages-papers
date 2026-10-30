module
public import LogicLineages.OrdinalComparison.WWGeneratedGradeDefinitions
public import Lean.Elab.Tactic.Omega

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source

def ordinalNumeral {Γ : List Ty} : Nat → OrdinalExpression Γ
  | 0 => .zero
  | 1 => .one
  | n + 2 => .add (ordinalNumeral (n + 1)) .one

abbrev OrdinalVector (Γ : List Ty) (m : Nat) := Fin (m + 1) → OrdinalExpression Γ

/-- Zero is inserted only outside the actual finite vector. -/
def ordinalVectorAt {Γ : List Ty} {m : Nat} (v : OrdinalVector Γ m) (i : Nat) :
    OrdinalExpression Γ := if h : i < m + 1 then v ⟨i, h⟩ else .zero

/-- The descending positive-coordinate box recursion. Only positive indices
are used by the actual box; the recursion terminates by distance to n+1. -/
def ordinalBoxPositive {Γ : List Ty} (n : Nat)
    (f g : Nat → OrdinalExpression Γ) (i : Nat) : OrdinalExpression Γ :=
  if h : i ≤ n then
    .emul (ordinalBoxPositive n f g (i + 1)) (.add (f i) (g i))
  else f i
termination_by n + 1 - i
decreasing_by omega

/-- Literal scalar association from paper05, with a separate n=0 case. -/
def ordinalBoxScalarTail {Γ : List Ty} (n : Nat) (f0 g0 : OrdinalExpression Γ) :
    OrdinalExpression Γ :=
  if n = 0 then .add f0 g0 else .add f0 (.add g0 (ordinalNumeral n))

def ordinalCanonicalBox {Γ : List Ty} {m n : Nat}
    (f : OrdinalVector Γ m) (g : OrdinalVector Γ n) : OrdinalVector Γ m :=
  fun i => if i.val = 0 then
    .collapse (ordinalBoxPositive n (ordinalVectorAt f) (ordinalVectorAt g) 1)
      (ordinalBoxScalarTail n (f 0) (g 0))
  else ordinalBoxPositive n (ordinalVectorAt f) (ordinalVectorAt g) i.val

end LogicLineages.OrdinalComparison.Source
