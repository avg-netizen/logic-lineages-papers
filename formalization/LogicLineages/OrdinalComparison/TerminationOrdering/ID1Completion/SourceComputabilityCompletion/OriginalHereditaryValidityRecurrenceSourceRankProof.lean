module
public import Mathlib.Data.Nat.Basic
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityRecurrenceSourceRankProof

/-- Ordinary natural-number rank induction with an independent runtime
parameter. The induction contains no concrete selector or machine code. -/
theorem binaryRankInduction (rank : Nat → Nat) (P Q : Nat → Nat → Prop)
    (step : ∀ value parameter,
      (∀ child childParameter, rank child < rank value → P child childParameter → Q child childParameter) →
      P value parameter → Q value parameter) :
    ∀ value parameter, P value parameter → Q value parameter := by
  have all : ∀ weight : Nat, ∀ value parameter, rank value = weight →
      P value parameter → Q value parameter := by
    intro weight
    induction weight using Nat.strong_induction_on with
    | h weight ih =>
      intro value parameter hw hp
      apply step value parameter
      · intro child childParameter hlt hc
        have hlt' : rank child < weight := by simpa only [hw] using hlt
        exact ih (rank child) hlt' child childParameter rfl hc
      · exact hp
  intro value parameter hp
  exact all (rank value) value parameter rfl hp

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityRecurrenceSourceRankProof
