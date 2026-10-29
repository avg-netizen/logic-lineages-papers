module

public import LogicLineages.Ultrafilters.UltrapowerDefinitions

@[expose] public section

namespace LogicLineages.Ultrafilters.Targets

/-- Paper 11, thm:main, including the actual quotient-domain consequence.
Field closure and well-definedness of the derivative are the separate source
proposition, not premises hidden in this properness theorem. -/
def UniversalUltrapowerProperness : Prop :=
  ∀ (p : Ultrafilter ℝ), Admissible p → ∃ f : ℝ → ℝ,
    (∀ x, 0 < f x ∧ f x ≤ 1) ∧
    (∀ η : ℝ, 0 < η → {x | f x < η} ∈ p) ∧
    (∀ g : ℝ → ℝ, Equivalent p f g → {x | ¬ ContinuousAt g x} ∈ p) ∧
    0 < classOf p f ∧
    (∀ η : ℝ, 0 < η → classOf p f < constantClass p η) ∧
    classOf p f ∉ differentiationDomain p ∧
    differentiationDomain p ≠ Set.univ

end LogicLineages.Ultrafilters.Targets
