module
public import LogicLineages.OrdinalComparison.ProfileReserveBudgetDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-! Paper07 lem:reserve (464–495): genuine leading monomials and literal R/H.
These targets do not assume or assert reserve consumption. -/
def ActualProfileLeadingMonomial : Prop :=
  ∀ rho : NONote, Order.IsSuccLimit rho.1.repr →
    ∃ beta : Ordinal.{0}, 0 < beta ∧ actualProfileLeadingMonomial rho = Ordinal.omega0 ^ beta ∧
      actualProfileLeadingMonomial rho ≤ rho.1.repr ∧
      actualProfileLeadingMonomial rho < epsilonZero ∧
      actualOrdinalNorm (actualProfileLeadingMonomial rho) = profileLeadingWeight rho

def ActualProfileReserveEligibility : Prop :=
  ∀ beta : Ordinal.{0}, 0 < beta → Ordinal.omega0 ^ beta < epsilonZero →
    ∀ rho : NONote, Order.IsSuccLimit rho.1.repr →
      actualProfileLeadingMonomial rho ≤ Ordinal.omega0 ^ beta →
      rho.1.repr < Ordinal.omega0 ^ beta * ((actualOrdinalNorm rho.1.repr + 1 : Nat) : Ordinal)

def ActualProfileReserveBudgetCalibration : Prop :=
  ∀ word : List NONote, (∀ rho ∈ word, Order.IsSuccLimit rho.1.repr) →
    profileReserveBlocks word = (word.map fun rho => actualOrdinalNorm rho.1.repr + 1).sum ∧
    profileReserveLeadingBound word =
      (word.map fun rho => actualOrdinalNorm (actualProfileLeadingMonomial rho)).foldr max 0

end LogicLineages.OrdinalComparison.Targets
