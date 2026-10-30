module
public import LogicLineages.ModelsAlgebra.PGroups.UlmTransportTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets

def groupIsomorphismFiniteFiltration : Prop :=
  ∀ (G H : Type) [AddCommGroup G] [AddCommGroup H] (e : G ≃+ H) (p j : ℕ),
    (finiteFiltration p j : AddSubgroup G).map e.toAddMonoidHom =
      (finiteFiltration p j : AddSubgroup H)

def groupIsomorphismUlmRank : Prop :=
  ∀ (G H : Type) [AddCommGroup G] [AddCommGroup H] (e : G ≃+ H) (p j : ℕ),
    Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j : AddSubgroup G)) =
      Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j : AddSubgroup H))

end LogicLineages.ModelsAlgebra.PGroups.Targets
