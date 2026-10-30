module
public import LogicLineages.OrdinalComparison.PrefixTraceDefinitions
public import LogicLineages.OrdinalComparison.ActualTerminalDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-! Actual endpoint transport and compensated finite-exit comparison for
paper07 reserve consumption. No endpoint or controller oracle is supplied. -/
def ActualPhiEndpointAlongTrace : Prop :=
  ∀ A : Ordinal.{0}, A < epsilonZero → ∀ i : Nat,
    i ≤ actualControlledCount Phi A →
    actualTerminalValue (actualControlledStateAfter Phi A i) = actualTerminalValue A

def ActualCompensatedExitDominatesTerminal : Prop :=
  ∀ A : Ordinal.{0}, A < epsilonZero → ∀ c : Nat,
    let g := compensatedPrefixControl c
    actualTerminalValue A ≤ actualOrdinalNorm
      (actualControlledStateAfter g A (actualControlledCount g A))

end LogicLineages.OrdinalComparison.Targets
