module
public import LogicLineages.PermittedControl.Definitions

@[expose] public section
namespace LogicLineages.PermittedControl.Targets

/-- Numerical prefix, distance and modular part of lemma control. Growth,
primitive recursiveness, factorial control and global comparison are separate. -/
def NearControlModular : Prop :=
  (∀ (b n : Nat), n ≤ b → nearControl b n = G n) ∧
  (∀ (b n : Nat), G n ≤ nearControl b n) ∧
  (∀ (b n : Nat), b < n → nearControl b n - G n < 2 * initialLcm n) ∧
  (∀ (b n : Nat), 2 ∣ nearControl b n) ∧
  (∀ (b m n : Nat), 0 < m → max m (b + 1) ≤ n →
    Int.ModEq (m : Int) (potential (nearControl b n) : Int) ((potential n : Int) - 1))

/-- Equation orbit-potential: arbitrary unbounded event count, actual near control. -/
def NearControlOrbit : Prop :=
  ∀ (b m t i : Nat), 0 < m → max m (b + 1) ≤ t →
    Int.ModEq (m : Int) (potential ((nearControl b)^[i] t) : Int)
      ((potential t : Int) - (i : Int))

end LogicLineages.PermittedControl.Targets
