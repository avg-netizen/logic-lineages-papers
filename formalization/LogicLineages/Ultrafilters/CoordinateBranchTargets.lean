module

public import LogicLineages.Ultrafilters.DecayDefinitions

@[expose] public section

namespace LogicLineages.Ultrafilters.Targets

/-- The complete first branch of paper 11's witness construction, with the
actual rational coordinate and explicit positive real-valued function. -/
def NonprincipalCoordinateWitness : Prop :=
  ∀ (p : Ultrafilter ℝ), Admissible p → ∀ h : ℝ →+ ℚ,
    (∀ s : Set ℚ, s.Finite → s ∉ Ultrafilter.map h p) →
    let f : ℝ → ℝ := fun x => rationalDecay (h x)
    (∀ x, 0 < f x ∧ f x ≤ 1) ∧
      (∀ η : ℝ, 0 < η → {x | f x < η} ∈ p) ∧
        DropsOnLargeTranslations p f

end LogicLineages.Ultrafilters.Targets
