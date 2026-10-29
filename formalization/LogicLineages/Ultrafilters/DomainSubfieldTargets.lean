module

public import LogicLineages.Ultrafilters.UltrapowerDefinitions
public import Mathlib.Order.Filter.FilterProduct
public import Mathlib.Algebra.Field.Subfield.Basic

@[expose] public section

namespace LogicLineages.Ultrafilters.Targets

/-- The subfield assertion of paper 11, prop:well-defined, with the actual
existential-over-representatives domain and the source's constant inclusion. -/
def DomainSubfield : Prop :=
  ∀ (p : Ultrafilter ℝ), Admissible p →
    ∃ K : Subfield (RealUltrapower p),
      (K : Set (RealUltrapower p)) = differentiationDomain p ∧
      ∀ r : ℝ, constantClass p r ∈ K

end LogicLineages.Ultrafilters.Targets
