module
@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowPresentationClauses

/-- The four numeral checks in source, certificate, destination order. -/
structure Checks where
  scalar : Nat → Bool
  multiset : Nat → Bool
  positive : Nat → Nat → Nat → Bool
  direct : Nat → Nat → Nat → Bool

def clause (domain : Nat → Bool) (edge : Nat → Nat → Nat → Bool)
    (tag : Nat → Nat) (P : Nat → Prop) (x : Nat) : Prop :=
  domain x = true ∧ ∀ y, (∃ cert, edge x cert y = true) → P (tag y)

def tagged (f : Checks) (P : Nat → Prop) (z : Nat) : Prop :=
  (∃ x, z = 2*x ∧ clause f.scalar f.positive (fun y => 2*y) P x) ∨
  (∃ x, z = 2*x+1 ∧ clause f.multiset f.direct (fun y => 2*y+1) P x)

def terms (f : Checks) (P : Nat → Prop) : Prop :=
  ∀ x, f.scalar x = true → P (2*x)

end LogicLineages.PersistentMarking.NumberedWindowPresentationClauses
