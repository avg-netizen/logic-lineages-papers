module

public import LogicLineages.Ultrafilters.HamelBranchDefinitions

@[expose] public section

namespace LogicLineages.Ultrafilters.Targets

/-- The complete second case of paper 11's explicit witness construction. -/
def VanishingCoordinateWitness : Prop :=
  ∀ {ι : Type*} (B : Module.Basis ι ℚ ℝ) (p : Ultrafilter ℝ),
    Admissible p → (∀ i, {x | B.repr x i = 0} ∈ p) →
      (∀ x, 0 < supportDecay B x ∧ supportDecay B x ≤ 1) ∧
        (∀ η : ℝ, 0 < η → {x | supportDecay B x < η} ∈ p) ∧
          DropsOnLargeTranslations p (supportDecay B)

end LogicLineages.Ultrafilters.Targets
