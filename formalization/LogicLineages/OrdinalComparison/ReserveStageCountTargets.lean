module
public import LogicLineages.OrdinalComparison.ReserveStageInputTargets
public import LogicLineages.OrdinalComparison.PrefixTraceDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-! Genuine numerical and count suppliers for paper07 lem:stage (436–462). -/
def ActualReserveIterationGap : Prop :=
  ∀ c X x d C : Nat, c ≤ X → x ≤ X → d + 1 ≤ C →
    (Phi^[d]) x + d < (Phi^[C]) X - c

def ActualReserveStageCountLowerBound : Prop :=
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
      D + 1 ≤ C

end LogicLineages.OrdinalComparison.Targets
