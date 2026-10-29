module
public import LogicLineages.Ultrafilters.Definitions

@[expose] public section

namespace LogicLineages.Ultrafilters.Targets

/-- Paper 11's actual coordinate-image dichotomy, before its construction.
The image is either principal at zero or excludes every finite rational set. -/
def CoordinateImageDichotomy : Prop :=
  ∀ (p : Ultrafilter ℝ), Admissible p → ∀ h : ℝ →+ ℚ,
    AdditivelyIdempotent (Ultrafilter.map h p) ∧
      (Ultrafilter.map h p = pure 0 ∨
        ∀ s : Set ℚ, s.Finite → s ∉ Ultrafilter.map h p)

end LogicLineages.Ultrafilters.Targets
