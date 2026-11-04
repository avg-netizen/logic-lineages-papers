module
public import LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticAccessibilityTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticAccessibilityProof
open PositiveArithmeticOperators PositiveArithmeticLeastSet PositiveArithmeticAccessibility

theorem leastImpliesAccessibility : PositiveArithmeticAccessibilityTargets.ActualLeastImpliesAccessibility := by
  intro body context Carrier R hcal x hx
  have hcarrier := (hcal (fun y => y ∈ leastSet body context) x).mp
    ((PositiveArithmeticLeastSetProof.semanticLeastUnfolding body context x).mp hx)
  refine ⟨hcarrier.1,?_⟩
  have hleast := PositiveArithmeticLeastSetProof.semanticLeastness body context
    {z | Acc (fun successor source => R source successor) z} (by
      intro z hz
      have hs := (hcal (fun y => Acc (fun successor source => R source successor) y) z).mp hz
      exact Acc.intro z (fun y hy => hs.2 y hy))
  exact hleast hx

theorem preservedCarrierAccessibility : PositiveArithmeticAccessibilityTargets.ActualPreservedCarrierAccessibility := by
  intro body context Carrier R hcal hpres x
  constructor
  · exact leastImpliesAccessibility body context Carrier R hcal x
  · rintro ⟨hc,ha⟩
    induction ha with
    | intro x hacc ih =>
      apply (PositiveArithmeticLeastSetProof.semanticLeastUnfolding body context x).mpr
      apply (hcal (fun y => y ∈ leastSet body context) x).mpr
      refine ⟨hc,?_⟩
      intro y hy
      exact ih y hy (hpres x y hc hy)

end LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticAccessibilityProof
