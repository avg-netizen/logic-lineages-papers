module

public import LogicLineages.Ultrafilters.DomainSubfieldTargets
public import Mathlib.RingTheory.Derivation.Basic

@[expose] public section

namespace LogicLineages.Ultrafilters.Targets

/-- Paper 11, prop:well-defined: the actual domain is a subfield, and ordinary
representative differentiation induces a derivation to the ultrapower.
The integer base expresses an ordinary derivation, without assuming a real
algebra structure or real-linearity. All real constants are represented. -/
def DomainDerivation : Prop :=
  ∀ (p : Ultrafilter ℝ), Admissible p →
    ∃ K : Subfield (RealUltrapower p),
      (K : Set (RealUltrapower p)) = differentiationDomain p ∧
      (∀ r : ℝ, constantClass p r ∈ K) ∧
      ∃ D : Derivation ℤ K (RealUltrapower p),
        ∀ (f : ℝ → ℝ)
          (hf : {x | DifferentiableAt ℝ f x} ∈ p)
          (hk : classOf p f ∈ K),
          D ⟨classOf p f, hk⟩ = classOf p (deriv f)

end LogicLineages.Ultrafilters.Targets
