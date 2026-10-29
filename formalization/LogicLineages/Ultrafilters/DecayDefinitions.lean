module

public import LogicLineages.Ultrafilters.Definitions
public import Mathlib.Data.Rat.Encodable

@[expose] public section

namespace LogicLineages.Ultrafilters

/-- An injective natural encoding is sufficient; it need not enumerate every
natural number. This is the paper's positive countable-coordinate decay. -/
noncomputable def rationalDecay (r : ℚ) : ℝ :=
  (1 / 2 : ℝ) ^ (Encodable.encode r + 1)

end LogicLineages.Ultrafilters
