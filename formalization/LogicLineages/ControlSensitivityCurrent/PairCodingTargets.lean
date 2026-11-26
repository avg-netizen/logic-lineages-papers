module
public import Mathlib.Data.Multiset.Basic
public import Mathlib.Order.Monotone.Basic
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.PairCodingTargets
/-- Pure supporting arithmetic; final source theorem must derive these hypotheses. -/
def PairCoding : Prop := ∀ q : Nat → Nat,
  (∀ n, 0 < q n) → (∀ n, 2 * q n < q (n+1)) → ∀ a b c d : Nat,
    q a + q b = q c + q d ↔ ({a,b} : Multiset Nat) = {c,d}

def SortedWitness : Prop := ∀ q : Nat → Nat,
  (∀ n, 0 < q n) → (∀ n, 2 * q n < q (n+1)) → ∀ a b low high difference : Nat,
    (q a + q b = q low + q high ∧ low + difference = high) ↔
      low = min a b ∧ high = max a b ∧ difference = max a b - min a b
end LogicLineages.ControlSensitivityCurrent.PairCodingTargets
