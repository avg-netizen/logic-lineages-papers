module
public import LogicLineages.OrdinalComparison.ProfileReserveBudgetDefinitions
public import LogicLineages.OrdinalComparison.ProfileCompilerDefinitions
public import LogicLineages.OrdinalComparison.ActualTerminalDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-! Paper07 lem:reserve (464–495): genuine stage-by-stage word consumption.
Empty words retain their finite equality; strictness is only for nonempty words. -/
def ActualProfileReserveWordConsumer : Prop :=
  ∀ beta : Ordinal.{0}, 0 < beta → Ordinal.omega0 ^ beta < epsilonZero →
    ∀ word : List NONote,
      (∀ rho ∈ word, Order.IsSuccLimit rho.1.repr ∧
        actualProfileLeadingMonomial rho ≤ Ordinal.omega0 ^ beta) → ∀ n : Nat,
      let initial := Ordinal.omega0 ^ beta * ((profileReserveBlocks word : Nat) : Ordinal) + (n : Ordinal)
      actualProfileWordValue word n ≤ actualTerminalValue initial ∧
      (word ≠ [] → actualProfileWordValue word n < actualTerminalValue initial)

end LogicLineages.OrdinalComparison.Targets
