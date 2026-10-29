module

public import LogicLineages.Ultrafilters.Definitions
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-! Independent paper-11 statements. The full universal properness target
is specified now and remains pending until its actual witness is constructed. -/
@[expose] public section

namespace LogicLineages.Ultrafilters.Targets

def PersistentDiscontinuity : Prop :=
  ∀ (p : Ultrafilter ℝ), Admissible p → ∀ f : ℝ → ℝ,
    (∀ x, 0 < f x) → DropsOnLargeTranslations p f →
    ∀ g : ℝ → ℝ, Equivalent p f g → {x | ¬ ContinuousAt g x} ∈ p

def UniversalPropernessWitness : Prop :=
  ∀ (p : Ultrafilter ℝ), Admissible p → ∃ f : ℝ → ℝ,
    (∀ x, 0 < f x ∧ f x ≤ 1) ∧
    (∀ η : ℝ, 0 < η → {x | f x < η} ∈ p) ∧
    ∀ g : ℝ → ℝ, Equivalent p f g → {x | ¬ ContinuousAt g x} ∈ p

end LogicLineages.Ultrafilters.Targets
