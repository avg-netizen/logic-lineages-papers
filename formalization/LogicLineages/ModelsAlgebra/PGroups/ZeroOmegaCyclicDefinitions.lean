module
public import LogicLineages.ModelsAlgebra.PGroups.TransfiniteDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.UlmDefinitions
public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.Data.ZMod.Basic
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
/-- Actual heterogeneous direct sum with one cyclic p^(n+1) summand per
member of the declared multiplicity type I n. -/
abbrev ZeroOmegaCyclicSum (p:ℕ) (I:ℕ→Type) :=
  DirectSum (Σn:ℕ,I n) (fun i=>ZMod (p^(i.1+1)))
end LogicLineages.ModelsAlgebra.PGroups
