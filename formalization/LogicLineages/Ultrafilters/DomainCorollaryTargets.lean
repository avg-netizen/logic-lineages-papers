module

public import LogicLineages.Ultrafilters.DomainSubfieldTargets
public import Mathlib.Order.Interval.Set.Defs

@[expose] public section
namespace LogicLineages.Ultrafilters.Targets

/-- Paper 11, corollary at lines 273–280: the actual differentiation domain
is a proper subfield containing all real constant classes, but is not order convex. -/
def DomainCorollary : Prop :=
  ∀ (p : Ultrafilter ℝ), Admissible p →
    ∃ K : Subfield (RealUltrapower p),
      (K : Set (RealUltrapower p)) = differentiationDomain p ∧
      (∀ r : ℝ, constantClass p r ∈ K) ∧
      (K : Set (RealUltrapower p)) ≠ Set.univ ∧
      ¬ Set.OrdConnected (K : Set (RealUltrapower p))

end LogicLineages.Ultrafilters.Targets
