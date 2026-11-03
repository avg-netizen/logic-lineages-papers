module
public import LogicLineages.OrdinalComparison.CommonHeadCollectedRowDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.CommonHeadCollectedRow.Targets
open CommonHeadLargeRow

/-- Arbitrary evaluators, not independent head values supplied by an oracle. -/
def ExactWeightedCollection : Prop := ∀ (row : Row) (f : Nat → Int),
  weighted f (collect row) = weighted f row

/-- Literal block provenance, zero deletion, distinctness, and original mass budget. -/
def LiteralCollectedSupport : Prop := ∀ row : Row,
  (collect row).Pairwise (fun a b => a.2≠b.2) ∧
  (∀ a∈collect row, a.1≠0 ∧ a.1=coefficient row a.2 ∧ ∃ b∈row, b.2=a.2) ∧
  mass (collect row) ≤ mass row

/-- The ORIGINAL threshold suffices after arbitrary equal-input cancellation.
Canceled inputs above the greatest surviving block do not control the sign. -/
def ActualCollectedDominance : Prop := ∀ (lam : Ordinal), lam<epsilonZero → Order.IsSuccLimit lam →
  ∀ (K : Int) (row : Row),
  (∀ a∈row, actualOrdinalNorm lam≤a.2 ∧ threshold K row≤a.2) →
  (collect row=[] → value lam K row=K) ∧
  (collect row≠[] → ∃ a∈collect row,
    (∀ b∈collect row, b.2≤a.2) ∧ Int.sign (value lam K row)=Int.sign a.1) ∧
  (∀ a∈collect row, (∀ b∈collect row, b.2≤a.2) →
    Int.sign (value lam K row)=Int.sign a.1)
end LogicLineages.OrdinalComparison.CommonHeadCollectedRow.Targets
