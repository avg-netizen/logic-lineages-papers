module
public import LogicLineages.OrdinalComparison.CommonHeadLargeRowDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.CommonHeadLargeRow.Targets

/-- Numerical arithmetic supplier at the literal printed threshold. The
actual head theorem below discharges every band and index premise. -/
def NumericalDominance : Prop := ∀ (K : Int) (row : NumericalRow),
  row.Pairwise (fun a b => a.2.2≠b.2.2) →
  (∀ a∈row, numericalThreshold K row ≤ a.2.2 ∧ Phi a.2.2<a.2.1 ∧ a.2.1<2*Phi a.2.2) →
  ∀ a∈row, a.1≠0 → (∀ b∈row, b.2.2≤a.2.2) →
    Int.sign (numericalValue K row) = Int.sign a.1

/-- Actual common-head row after equal-input collection. Every remaining
input is genuine and above exactly L. Only the selected largest coefficient
must be nonzero; other zero coefficients do not invalidate the estimate.
Collection and removal of canceled larger blocks remain separate suppliers. -/
def ActualHeadDominance : Prop := ∀ (lam : Ordinal), lam<epsilonZero → Order.IsSuccLimit lam →
  ∀ (K : Int) (row : Row), row.Pairwise (fun a b => a.2≠b.2) →
  (∀ a∈row, actualOrdinalNorm lam≤a.2 ∧ threshold K row≤a.2) →
  ∀ a∈row, a.1≠0 → (∀ b∈row, b.2≤a.2) →
    Int.sign (value lam K row) = Int.sign a.1
end LogicLineages.OrdinalComparison.CommonHeadLargeRow.Targets
