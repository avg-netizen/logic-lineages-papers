module

public import LogicLineages.ModelsAlgebra.PGroups.PrimeSquareDefinitions
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finsupp.Encodable
public import Mathlib.Algebra.Group.Prod

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

/-- One short cyclic summand and countably many p-squared cyclic summands. -/
abbrev ShiftGroup (p : ℕ) := ZMod p × (ℕ →₀ ZMod (p ^ 2))

/-- Literal source self-map: insert the short generator at coordinate zero,
shift all long coordinates one step, and leave the short output zero. -/
noncomputable def shiftHom (p : ℕ) : ShiftGroup p →+ ShiftGroup p :=
  let insert : ZMod p →+ (ℕ →₀ ZMod (p ^ 2)) :=
    (Finsupp.singleAddHom 0).comp (primeSquareInclusion p)
  let tail : (ℕ →₀ ZMod (p ^ 2)) →+ (ℕ →₀ ZMod (p ^ 2)) :=
    Finsupp.mapDomain.addMonoidHom Nat.succ
  (0 : ShiftGroup p →+ ZMod p).prod
    (insert.comp (AddMonoidHom.fst _ _) + tail.comp (AddMonoidHom.snd _ _))

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
