module
public import LogicLineages.ModelsAlgebra.PGroups.UlmDefinitions
public import Mathlib.LinearAlgebra.Dimension.Basic
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets

def groupInjectiveSocleMap : Prop :=
  ∀ (G H : Type) [AddCommGroup G] [AddCommGroup H] (p : ℕ) (S : AddSubgroup G)
    (f : G →+ H), Function.Injective f →
      (pSocle p S).map f = pSocle p (S.map f)

def groupInjectiveUlmIsomorphism : Prop :=
  ∀ (G H : Type) [AddCommGroup G] [AddCommGroup H] (p : ℕ) (S : AddSubgroup G)
    (f : G →+ H), Function.Injective f →
      Nonempty (UlmLayer p S ≃ₗ[ZMod p] UlmLayer p (S.map f))

end LogicLineages.ModelsAlgebra.PGroups.Targets
