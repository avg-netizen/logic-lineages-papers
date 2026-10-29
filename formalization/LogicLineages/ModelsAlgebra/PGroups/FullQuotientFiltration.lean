module

public import LogicLineages.ModelsAlgebra.PGroups.FullQuotientTargets
public import LogicLineages.ModelsAlgebra.PGroups.UlmIsomorphism
public import LogicLineages.ModelsAlgebra.PGroups.OmegaCutFacts

@[expose] public section

/-!
# Both conclusions of the source quotient-filtration lemma

The actual ordinal cut supplies the local second-successor kernel
condition, which gives the bijective induced Ulm map. Its linear
equivalence then yields the rank identity by Mathlib's proved rank
invariance. No isomorphism or dimension theorem is supplied as an input.
-/

namespace LogicLineages.ModelsAlgebra.PGroups

universe u v

variable {G : Type u} [AddCommGroup G]

theorem full_quotient_filtration (p : ℕ) [Fact p.Prime] (T : AddSubgroup G)
    (γ : Ordinal.{v}) (hT : T ≤ transfiniteFiltration p (Ordinal.omega0 * γ)) :
    (∀ α ≤ Ordinal.omega0 * γ,
      (transfiniteFiltration p α : AddSubgroup (G ⧸ T)) =
        (transfiniteFiltration p α : AddSubgroup G).map (QuotientAddGroup.mk' T)) ∧
    ∀ β (hβ : β < Ordinal.omega0 * γ),
      Function.Bijective (quotientUlmMap p T (Ordinal.omega0 * γ) hT β hβ.le) ∧
      Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p β : AddSubgroup G)) =
        Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p β : AddSubgroup (G ⧸ T))) := by
  refine ⟨quotient_filtration_below p T (Ordinal.omega0 * γ) hT, ?_⟩
  intro β hβ
  let S : AddSubgroup G := transfiniteFiltration p β
  let f : G →+ G ⧸ T := QuotientAddGroup.mk' T
  have hdeep : f.ker ≤ pStep p (pStep p S) :=
    omegaCut_kernel_le_secondStep p T γ hT hβ
  let e₁ : UlmLayer p S ≃ₗ[ZMod p] UlmLayer p (S.map f) :=
    LinearEquiv.ofBijective (ulmMap p S f) (UlmLocal.ulmMap_bijective p S f hdeep)
  let e₂ : UlmLayer p (S.map f) ≃ₗ[ZMod p]
      UlmLayer p (transfiniteFiltration p β : AddSubgroup (G ⧸ T)) :=
    ulmLayerCongr p (quotient_filtration_below p T (Ordinal.omega0 * γ) hT β hβ.le).symm
  have hbij : Function.Bijective (quotientUlmMap p T (Ordinal.omega0 * γ) hT β hβ.le) := by
    change Function.Bijective (fun x => e₂ (e₁ x))
    exact e₂.bijective.comp e₁.bijective
  exact ⟨hbij, (e₁.trans e₂).rank_eq⟩

end LogicLineages.ModelsAlgebra.PGroups
