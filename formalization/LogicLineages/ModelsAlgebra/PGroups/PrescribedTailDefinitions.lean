module
public import LogicLineages.ModelsAlgebra.PGroups.ReducedLengthDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.LocalSocleBFDefinitions
public import Mathlib.GroupTheory.QuotientGroup.Defs
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
/-- The literal omega-block Ulm factor, not an assigned invariant. -/
abbrev UlmFactor (p:ℕ) (G:Type) [AddCommGroup G] (ξ:Ordinal.{0}) :=
  (transfiniteFiltration p (Ordinal.omega0*ξ):AddSubgroup G) ⧸
    (transfiniteFiltration p (Ordinal.omega0:Ordinal.{0}):
      AddSubgroup (transfiniteFiltration p (Ordinal.omega0*ξ):AddSubgroup G))
end LogicLineages.ModelsAlgebra.PGroups
