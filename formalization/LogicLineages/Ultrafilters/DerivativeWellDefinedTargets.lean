module

public import LogicLineages.Ultrafilters.UltrapowerDefinitions

@[expose] public section

namespace LogicLineages.Ultrafilters.Targets

/-- The first assertion of paper 11, prop:well-defined. The actual quotient
and ordinary derivatives are used. Total `deriv` values outside the large
sets of differentiability points have no effect on the quotient conclusion.
Subfield closure and the derivation laws are separate pending obligations. -/
def DerivativeWellDefined : Prop :=
  ∀ (p : Ultrafilter ℝ), Admissible p → ∀ f g : ℝ → ℝ,
    classOf p f = classOf p g →
    {x | DifferentiableAt ℝ f x} ∈ p →
    {x | DifferentiableAt ℝ g x} ∈ p →
    classOf p (deriv f) = classOf p (deriv g)

end LogicLineages.Ultrafilters.Targets
