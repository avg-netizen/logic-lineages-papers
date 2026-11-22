module
public import LogicLineages.PersistentMarking.NumberedWindowCoverAlgorithm

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowCoverGrammarMonotone
open NumberedWindowCoverAlgorithm (grammar)

/-- Membership transport in both genuine ordered grammar lists. The heads
and types are unchanged; only the maximum numeral and depth may increase.
No order, multiplicity, or same-output-list identity is asserted. -/
def ExactGrammarBoundsInclusion : Prop :=
  ∀ (H K : List Nat) (smallNumeral largeNumeral smallDepth largeDepth : Nat),
    smallNumeral ≤ largeNumeral → smallDepth ≤ largeDepth →
      (grammar H K smallNumeral smallDepth).1 ⊆ (grammar H K largeNumeral largeDepth).1 ∧
      (grammar H K smallNumeral smallDepth).2 ⊆ (grammar H K largeNumeral largeDepth).2

end LogicLineages.PersistentMarking.NumberedWindowCoverGrammarMonotone
