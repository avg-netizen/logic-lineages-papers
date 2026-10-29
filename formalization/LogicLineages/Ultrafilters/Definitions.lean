module

public import Mathlib.Order.Filter.Ultrafilter.Basic
public import Mathlib.Data.Real.Basic

@[expose] public section

namespace LogicLineages.Ultrafilters

def translate {G : Type*} [Add G] (s : Set G) (x : G) : Set G :=
  {y | x + y ∈ s}

/-- Exact membership equation for p+p=p, without a supplied semigroup theorem. -/
def AdditivelyIdempotent {G : Type*} [Add G] (p : Ultrafilter G) : Prop :=
  ∀ s : Set G, s ∈ p ↔ {x | translate s x ∈ p} ∈ p

def NearZero (p : Ultrafilter ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → Set.Ioo 0 ε ∈ p

def Admissible (p : Ultrafilter ℝ) : Prop :=
  AdditivelyIdempotent p ∧ NearZero p

def star {G : Type*} [Add G] (p : Ultrafilter G) (s : Set G) : Set G :=
  s ∩ {x | translate s x ∈ p}

def Equivalent (p : Ultrafilter ℝ) (f g : ℝ → ℝ) : Prop :=
  {x | g x = f x} ∈ p

def DropsOnLargeTranslations (p : Ultrafilter ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ (T : Set ℝ), T ∈ p → ∀ x ∈ star p T, ∀ δ : ℝ, 0 < δ →
    ∃ y : ℝ, y ∈ translate T x ∧ y ∈ Set.Ioo 0 δ ∧ f (x + y) < f x / 2

end LogicLineages.Ultrafilters
