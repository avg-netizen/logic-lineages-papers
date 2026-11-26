module
public import LogicLineages.PermittedControl.InitialPeelingDefinitions

@[expose] public section
namespace LogicLineages.PermittedControl.Targets
open OrdinalComparison

/-- Whole initial original-unit phase, excluding the final leading unit.
Either source exception/no-sensitive/equal-shift passes with genuine common
first hits and norm clocks, or source sign is realized before that unit.
Neither original/generated traversal nor synchronized return is supplied. -/
def ActualInitialPeeling : Prop := ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (mu nu delta A A' : Ordinal.{0}) (t : Nat),
  mu < epsilonZero → nu < epsilonZero → delta < epsilonZero →
  A < epsilonZero → A' < epsilonZero →
  (mu=0 ∨ Order.IsSuccLimit mu) → (nu=0 ∨ Order.IsSuccLimit nu) →
  Order.IsSuccLimit delta →
  thickBlockTail (initialPeelingRadius mu nu delta) B ≤ t →
  actualLimitPart A=mu+delta → actualLimitPart A'=nu+delta →
  actualOrdinalNorm A=t → actualOrdinalNorm A'=t →
  (initialPeelingPass mu nu delta → ∃ i : Nat,
    FirstEntry f A (mu+Ordinal.omega0^(Ordinal.log Ordinal.omega0 delta)) i ∧
    FirstEntry f A' (nu+Ordinal.omega0^(Ordinal.log Ordinal.omega0 delta)) i ∧
    actualOrdinalNorm ((descentWith f)^[i] A)=f^[i] t ∧
    actualOrdinalNorm ((descentWith f)^[i] A')=f^[i] t) ∧
  (¬ initialPeelingPass mu nu delta → ∃ i : Nat,
    actualLimitPart ((descentWith f)^[i] A-mu) ≠ actualLimitPart ((descentWith f)^[i] A'-nu) ∧
    compare (actualLimitPart ((descentWith f)^[i] A-mu)) (actualLimitPart ((descentWith f)^[i] A'-nu)) =
      compare (relativeProfile nu (Ordinal.log Ordinal.omega0 delta))
        (relativeProfile mu (Ordinal.log Ordinal.omega0 delta)) ∧
    Ordinal.omega0^(Ordinal.log Ordinal.omega0 delta) ≤ actualLimitPart ((descentWith f)^[i] A-mu) ∧
    Ordinal.omega0^(Ordinal.log Ordinal.omega0 delta) ≤ actualLimitPart ((descentWith f)^[i] A'-nu))

end LogicLineages.PermittedControl.Targets
