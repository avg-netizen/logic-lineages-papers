module

public import Mathlib.Algebra.Module.Equiv.Defs
public import LogicLineages.ModelsAlgebra.PGroups.QuotientFiltration
public import LogicLineages.ModelsAlgebra.PGroups.UlmMapDefinitions

@[expose] public section

/-!
# The literal quotient-map homomorphism between actual Ulm layers

The already checked filtration equality identifies the target layer of
the constructed image map with the actual quotient-group filtration
layer. This only constructs the homomorphism; it does not assert that
the map is bijective at a cut or give a dimension equality.
-/

namespace LogicLineages.ModelsAlgebra.PGroups

universe u v

variable {G : Type u} [AddCommGroup G]

noncomputable def ulmLayerCongr (p : ℕ) {S T : AddSubgroup G} (h : S = T) :
    UlmLayer p S ≃ₗ[ZMod p] UlmLayer p T := by
  cases h
  exact LinearEquiv.refl (ZMod p) _

noncomputable def quotientUlmMap (p : ℕ) (T : AddSubgroup G) (δ : Ordinal.{v})
    (hT : T ≤ transfiniteFiltration p δ) (β : Ordinal.{v}) (hβ : β ≤ δ) :
    UlmLayer p (transfiniteFiltration p β : AddSubgroup G) →ₗ[ZMod p]
      UlmLayer p (transfiniteFiltration p β : AddSubgroup (G ⧸ T)) :=
  (ulmLayerCongr p (quotient_filtration_below p T δ hT β hβ).symm).toLinearMap.comp
    (ulmMap p (transfiniteFiltration p β : AddSubgroup G) (QuotientAddGroup.mk' T))

end LogicLineages.ModelsAlgebra.PGroups
