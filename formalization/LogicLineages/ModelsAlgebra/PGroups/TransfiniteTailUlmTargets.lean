module
public import LogicLineages.ModelsAlgebra.PGroups.TransfiniteFiltration
public import LogicLineages.ModelsAlgebra.PGroups.UlmTransportTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
universe v

def groupTransfiniteTailUlmIsomorphism : Prop :=
  ∀ (G : Type) [AddCommGroup G] (p : ℕ) (δ β : Ordinal.{v}),
    Nonempty (UlmLayer p (transfiniteFiltration p β :
      AddSubgroup (transfiniteFiltration p δ : AddSubgroup G)) ≃ₗ[ZMod p]
      UlmLayer p (transfiniteFiltration p (δ+β) : AddSubgroup G))

def groupTransfiniteTailUlmRank : Prop :=
  ∀ (G : Type) [AddCommGroup G] (p : ℕ) (δ β : Ordinal.{v}),
    Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p β :
      AddSubgroup (transfiniteFiltration p δ : AddSubgroup G))) =
      Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p (δ+β) : AddSubgroup G))

end LogicLineages.ModelsAlgebra.PGroups.Targets
