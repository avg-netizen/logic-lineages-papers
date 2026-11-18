module
public import LogicLineages.OrdinalComparison.ControlResidueTargets
@[expose] public section
namespace LogicLineages.CartierObserverCurrent.FullResidueEnvelopes.Targets
open LogicLineages.OrdinalComparison

/-- Fixed explicit numerical witness, with genuine primitive recursion. -/
def CompleteEnvelopes : Prop :=
  (∀ m : Nat, 0 < m → fastControlResidue m < m) ∧
  Primrec fastControlResidue ∧
  (∀ m : Nat, 0 < m → ∀ x : Nat, m ≤ x →
    Nat.ModEq m (Phi x) (fastControlResidue m)) ∧
  (∀ m : Nat, 0 < m → ∀ s j : Nat, 1 ≤ s → 2 ≤ j → m ≤ 2 ^ (2 ^ s) →
    Nat.ModEq m (fastControl j s) (fastControlResidue m)) ∧
  (∀ m : Nat, 0 < m → ∀ u : Nat, m ≤ 2 ^ (2 ^ Phi u) →
    Nat.ModEq m (Phi (u + 1)) (fastControlResidue m))
end LogicLineages.CartierObserverCurrent.FullResidueEnvelopes.Targets
