module
public import LogicLineages.OrdinalComparison.ActualMaximumPredecessorDefinitions
public import LogicLineages.OrdinalComparison.ControlledCountDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-! Paper07 lem:stage (436–462), actual ordinal eligibility and first residual.
All edge cases k=0,n=0,m=1 remain. In particular c≤x is NOT assumed. -/
def ActualReserveStageDomain : Prop :=
  ∀ beta : Ordinal.{0}, 0 < beta → Ordinal.omega0 ^ beta < epsilonZero →
    ∀ k m n x : Nat, 1 ≤ m → ∀ rho : Ordinal.{0}, Order.IsSuccLimit rho →
      rho < Ordinal.omega0 ^ beta * (m : Ordinal) → actualOrdinalNorm rho ≤ x →
      x ≤ actualOrdinalNorm (Ordinal.omega0 ^ beta * ((k + m : Nat) : Ordinal) + (n : Ordinal)) →
      let pi := Ordinal.omega0 ^ beta
      let A := pi * ((k + m : Nat) : Ordinal) + (n : Ordinal)
      let X := actualOrdinalNorm A
      let c := k * actualOrdinalNorm pi
      let alpha := rho + ((x - actualOrdinalNorm rho : Nat) : Ordinal)
      A < epsilonZero ∧ X = (k + m) * actualOrdinalNorm pi + n ∧ c ≤ X ∧
      alpha < pi * (m : Ordinal) ∧ alpha < epsilonZero ∧
      actualOrdinalNorm alpha = x ∧ c + x < Phi X

def ActualReserveStageFirstResidual : Prop :=
  ∀ beta : Ordinal.{0}, 0 < beta → Ordinal.omega0 ^ beta < epsilonZero →
    ∀ k m n x : Nat, 1 ≤ m → ∀ rho : Ordinal.{0}, Order.IsSuccLimit rho →
      rho < Ordinal.omega0 ^ beta * (m : Ordinal) → actualOrdinalNorm rho ≤ x →
      x ≤ actualOrdinalNorm (Ordinal.omega0 ^ beta * ((k + m : Nat) : Ordinal) + (n : Ordinal)) →
      let pi := Ordinal.omega0 ^ beta
      let X := actualOrdinalNorm (pi * ((k + m : Nat) : Ordinal) + (n : Ordinal))
      let c := k * actualOrdinalNorm pi
      let alpha := rho + ((x - actualOrdinalNorm rho : Nat) : Ordinal)
      let Q := actualMaximumPredecessor (pi * (m : Ordinal)) (Phi X - c)
      alpha ≤ Q ∧ actualOrdinalNorm Q = Phi X - c ∧ x ≤ actualOrdinalNorm Q

end LogicLineages.OrdinalComparison.Targets
