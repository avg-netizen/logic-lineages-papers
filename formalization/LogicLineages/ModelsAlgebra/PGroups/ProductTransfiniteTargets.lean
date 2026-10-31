module
public import LogicLineages.ModelsAlgebra.PGroups.ProductTransfiniteDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
def productTransfiniteFiltration : Prop :=
  ∀ (p : ℕ) (G H : Type) [AddCommGroup G] [AddCommGroup H] (α : Ordinal.{0}),
    (transfiniteFiltration p α : AddSubgroup (G×H)) =
      (transfiniteFiltration p α : AddSubgroup G).prod (transfiniteFiltration p α : AddSubgroup H)
def productTransfiniteUlmRank : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G H : Type) [AddCommGroup G] [AddCommGroup H] (α : Ordinal.{0}),
    Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α : AddSubgroup (G×H))) =
      Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α : AddSubgroup G)) +
      Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α : AddSubgroup H))
end LogicLineages.ModelsAlgebra.PGroups.Targets
