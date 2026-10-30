module
public import LogicLineages.OrdinalComparison.ReserveStageCountTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-! Full paper07 lem:stage (436–462), actual relative first-finite cut.
The relative count is not substituted by the global terminal count. -/
def FullActualOneStageReserve : Prop :=
  ∀ beta : Ordinal.{0}, 0 < beta → Ordinal.omega0 ^ beta < epsilonZero →
    ∀ k m n x : Nat, 1 ≤ m → ∀ rho : Ordinal.{0}, Order.IsSuccLimit rho →
      rho < Ordinal.omega0 ^ beta * (m : Ordinal) → actualOrdinalNorm rho ≤ x →
      x ≤ actualOrdinalNorm (Ordinal.omega0 ^ beta * ((k + m : Nat) : Ordinal) + (n : Ordinal)) →
      let pi := Ordinal.omega0 ^ beta
      let c := k * actualOrdinalNorm pi
      let R := pi * (m : Ordinal) + (n : Ordinal)
      let alpha := rho + ((x - actualOrdinalNorm rho : Nat) : Ordinal)
      let C := actualControlledCount (compensatedPrefixControl c) R
      let D := actualControlledCount Phi alpha
      let retained := pi * (k : Ordinal)
      let A := pi * ((k + m : Nat) : Ordinal) + (n : Ordinal)
      0 < C ∧
      (∀ i : Nat, i ≤ C → actualControlledStateAfter Phi A i =
        retained + actualControlledStateAfter (compensatedPrefixControl c) R i) ∧
      (∀ i : Nat, i < C → retained + Ordinal.omega0 ≤ actualControlledStateAfter Phi A i) ∧
      ∃ n' : Nat, actualControlledStateAfter Phi A C = retained + (n' : Ordinal) ∧
        (Phi^[D]) x + D < n'

end LogicLineages.OrdinalComparison.Targets
