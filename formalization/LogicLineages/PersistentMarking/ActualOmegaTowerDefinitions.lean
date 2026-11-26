module

public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.SetTheory.Ordinal.FixedPoint

@[expose] public section

namespace LogicLineages.PersistentMarking.ActualOmegaTower
open scoped Ordinal

/-- The paper's actual first uncountable ordinal, not a countable semantic value. -/
noncomputable def omegaIndex : Ordinal.{0} := ω₁

noncomputable def powerStep (a : Ordinal.{0}) : Ordinal.{0} := omegaIndex ^ a

/-- The literal index sequence: a₀ = 0 and aₙ₊₁ = Ω^aₙ. -/
noncomputable def argument (n : Nat) : Ordinal.{0} := powerStep^[n] 0

/-- The actual ordinal supremum of the printed index sequence. -/
noncomputable def endpoint : Ordinal.{0} := ⨆ n : Nat, argument n

end LogicLineages.PersistentMarking.ActualOmegaTower
