module
public import LogicLineages.OrdinalComparison.ControlScheduleTargets
public import LogicLineages.OrdinalComparison.HeadEndpointDefinitions
public import LogicLineages.OrdinalComparison.CompatiblePrefixDefinitions
public import LogicLineages.OrdinalComparison.RestrictedPartitionTargets

@[expose] public section

/-! Exact actual ordinal/parameter suppliers for paper10 prop:omega-block.
The ordinal is literally omega^omega, the maximum is the original source
maximum, and the control is the original compensated Phi controller. -/

namespace LogicLineages.OrdinalComparison.Targets

def ActualOmegaOmegaFacts : Prop :=
  Ordinal.omega0 ^ Ordinal.omega0 < epsilonZero ∧
    Order.IsSuccLimit (Ordinal.omega0.{0} ^ Ordinal.omega0.{0}) ∧
      actualOrdinalNorm (Ordinal.omega0 ^ Ordinal.omega0) = 3

def ActualOmegaOmegaMaximum : Prop :=
  ∀ b : Nat, 3 ≤ b → actualMaximumPredecessor (Ordinal.omega0 ^ Ordinal.omega0) b =
    Ordinal.omega0 ^ ((b - 1 : Nat) : Ordinal)

def RestrictedPartitionDoubleExponentBound : Prop :=
  ∀ B d m : Nat, 16 ≤ B → 1 ≤ d → d ≤ B → 1 ≤ m → m ≤ B →
    restrictedPartitionPeriod d m ≤ 2 ^ (2 ^ B)

def ActualOmegaBlockFirstStep : Prop :=
  ∀ c u : Nat, c + 3 ≤ u →
    let g := compensatedPrefixControl c
    let a := actualHeadInitial (Ordinal.omega0 ^ Ordinal.omega0) (u - c)
    let B := Phi u
    let d := B - c - 1
    1 ≤ d ∧
      actualControlledStep g a = Ordinal.omega0 ^ (d : Ordinal) ∧
      actualOrdinalNorm (actualControlledStep g a) = B - c ∧
      actualControlledCount g a = actualControlledCount g (Ordinal.omega0 ^ (d : Ordinal)) + 1

end LogicLineages.OrdinalComparison.Targets
