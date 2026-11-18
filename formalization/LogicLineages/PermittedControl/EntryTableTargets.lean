module
public import LogicLineages.PermittedControl.EntryDefinitions

@[expose] public section
namespace LogicLineages.PermittedControl.Targets
open OrdinalComparison

/-- All four displayed entry-field rows in controls.tex. The a=0 iterate
includes the uniterated E row. Values use modulus2m; counts/halves use m. -/
def DerivedEntryTable : Prop := ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (m : Nat) (lam nu : Ordinal.{0}) (t i : Nat), 0 < m → lam < epsilonZero →
    Order.IsSuccLimit lam → (nu = 0 ∨ Order.IsSuccLimit nu) → nu < lam →
    max (actualOrdinalNorm lam) (max (actualOrdinalNorm nu+3) (max m B)) ≤ t →
    FirstEntry f (countInitial lam t) nu i →
    (∀ k : Nat, 0 < k → lam = nu+Ordinal.omega0*(k : Ordinal) →
      Int.ModEq (m : Int) (i : Int) (k : Int) ∧
      (∀ a : Nat, Int.ModEq (2*(m : Int))
        (f^[a] (entryNormAt f (countInitial lam t) i) : Int)
        (2*(potential t : Int)-2*((k : Int)+(a : Int)))) ∧
      Int.ModEq (m : Int) (potential (f (entryNormAt f (countInitial lam t) i)) : Int)
        ((potential t : Int)-(k : Int)-1)) ∧
    ((¬ ∃ k : Nat, 0 < k ∧ lam = nu+Ordinal.omega0*(k : Ordinal)) →
      Int.ModEq (m : Int) (i : Int) ((potential t : Int)-(((actualOrdinalNorm nu+1)/2 : Nat) : Int)) ∧
      (∀ a : Nat, Int.ModEq (2*(m : Int))
        (f^[a] (entryNormAt f (countInitial lam t) i) : Int)
        (2*(((actualOrdinalNorm nu+1)/2 : Nat) : Int)-2*(a : Int))) ∧
      Int.ModEq (m : Int) (potential (f (entryNormAt f (countInitial lam t) i)) : Int)
        ((((actualOrdinalNorm nu+1)/2 : Nat) : Int)-1))

/-- Positive bare iterates obey the modular table. The uniterated identity
field is literal t, not 2*p(t); its odd bit is explicitly retained. -/
def BareIterateAndIdentityTable : Prop :=
  (∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B → ∀ (m t a : Nat),
    0 < m → max m B ≤ t → 0 < a →
    Int.ModEq (2*(m : Int)) (f^[a] t : Int) (2*(potential t : Int)-2*(a : Int))) ∧
  (∀ t : Nat, t = 2*potential t+t%2) ∧
  (∀ q : Nat, 2*potential (2*q+1) ≠ 2*q+1)

/-- Identity interval convention is realized by the actual first-hit semantics
and returns the literal input norm and zero events, including odd inputs. -/
def IdentityEntry : Prop :=
  ∀ (f : Nat → Nat) (nu : Ordinal.{0}) (t : Nat), nu < epsilonZero →
    (nu = 0 ∨ Order.IsSuccLimit nu) → actualOrdinalNorm nu ≤ t →
    FirstEntry f (countInitial nu t) nu 0 ∧ entryNormAt f (countInitial nu t) 0 = t

end LogicLineages.PermittedControl.Targets
