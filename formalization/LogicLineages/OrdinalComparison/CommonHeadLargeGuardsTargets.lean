module
public import LogicLineages.OrdinalComparison.CommonHeadLargeGuardsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.CommonHeadLargeGuards.Targets
open CommonHeadLargeRow CommonHeadCollectedRow

/-- Masks enumerate exactly the equality block of the actual labeled input. -/
def ExactBlockFormula : Prop := ∀ cs : List Int, ∀ i desired ν,
  (blockFormula cs i desired).eval ν ↔
    Int.sign (coefficient (inputRow cs ν) (ν i))=desired

/-- No fresh input name is introduced by finite guard construction. -/
def OriginalInputSupport : Prop := ∀ K cs desired, ∀ i∈(largeFormula K cs desired).variables,
  i<cs.length

/-- The literal finite formula uses original inputs only. It handles all-zero
cancellation, largest surviving blocks, and any signed desired result. -/
def ExactActualLargeFormula : Prop := ∀ (lam : Ordinal), lam<epsilonZero → Order.IsSuccLimit lam →
  ∀ (K : Int) (cs : List Int) (desired : Int) (ν : Nat → Nat),
  (∀ i<cs.length, actualOrdinalNorm lam≤ν i) →
  ((largeFormula K cs desired).eval ν ↔
    (∀ i<cs.length, originalThreshold K cs≤ν i) ∧
    Int.sign (value lam K (inputRow cs ν))=desired)
end LogicLineages.OrdinalComparison.CommonHeadLargeGuards.Targets
