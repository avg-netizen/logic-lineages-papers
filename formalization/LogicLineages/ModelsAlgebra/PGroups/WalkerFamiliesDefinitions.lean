module
public import LogicLineages.ModelsAlgebra.PGroups.WalkerReservoirDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
/-- Source eq:odd-group; a binary product is the finite direct sum. -/
abbrev WalkerOdd (p : ℕ) (δ : Ordinal.{0}) (r : ℕ) :=
  WalkerLowerReservoir p δ × DirectSum (Fin r) (fun _ => WalkerSourceGroup p δ)
/-- Source eq:even-group. -/
abbrev WalkerEven (p : ℕ) (δ : Ordinal.{0}) (r : ℕ) :=
  WalkerOdd p δ r × DirectSum ℕ (fun _ => WalkerSourceGroup p (δ+1))
end LogicLineages.ModelsAlgebra.PGroups
