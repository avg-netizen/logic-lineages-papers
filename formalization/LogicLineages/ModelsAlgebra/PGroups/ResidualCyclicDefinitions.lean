module
public import LogicLineages.ModelsAlgebra.PGroups.UlmRankAssemblyTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

abbrev ResidualCyclicProduct (p N : ℕ) (I : Fin N → Type) (a b : Fin N) :=
  (l : {l : Fin N // l ≠ a ∧ l ≠ b}) → (I l.val →₀ ZMod (p ^ (l.val.val + 1)))

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
