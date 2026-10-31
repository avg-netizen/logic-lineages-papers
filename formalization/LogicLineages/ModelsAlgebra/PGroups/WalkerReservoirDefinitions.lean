module
public import LogicLineages.ModelsAlgebra.PGroups.WalkerCompleteDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.DirectSumFiltrationDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
/-- The literal source lower reservoir, indexed by every ordinal below δ and ω copies. -/
abbrev WalkerLowerReservoir (p : ℕ) (δ : Ordinal.{0}) :=
  DirectSum (δ.ToType × ℕ) (fun i => WalkerSourceGroup p (Ordinal.typein (α := δ.ToType) (· < ·) i.1))
end LogicLineages.ModelsAlgebra.PGroups
