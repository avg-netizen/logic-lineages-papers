module
public import LogicLineages.ModelsAlgebra.PGroups.CutAmalgamationDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
universe u v

def cutAmalgamation : Prop :=
  ∀ (G H : Type u) [AddCommGroup G] [AddCommGroup H] (p : ℕ) (δ : Ordinal.{v})
    (B L : AddSubgroup G) (f : B →+ H) (g : L →+ H),
    Function.Injective f → Function.Injective g →
    L ≤ (transfiniteFiltration p δ : AddSubgroup G) →
    B ⊓ transfiniteFiltration p δ ≤ L →
    (∀ x : L, g x ∈ (transfiniteFiltration p δ : AddSubgroup H)) →
    (∀ (x : G) (hb : x ∈ B) (hl : x ∈ L), f ⟨x,hb⟩ = g ⟨x,hl⟩) →
    (∀ (b : B) (β : Ordinal.{v}), β ≤ δ →
      (f b ∈ (transfiniteFiltration p β : AddSubgroup H) ↔
        (b:G) ∈ (transfiniteFiltration p β : AddSubgroup G))) →
    ∃ F : ↥(B ⊔ L) →+ H, Function.Injective F ∧
      (∀ b : B, F ⟨b,(le_sup_left : B ≤ B ⊔ L) b.property⟩ = f b) ∧
      (∀ l : L, F ⟨l,(le_sup_right : L ≤ B ⊔ L) l.property⟩ = g l) ∧
      ∀ (x : ↥(B ⊔ L)) (β : Ordinal.{v}), β ≤ δ →
        (F x ∈ (transfiniteFiltration p β : AddSubgroup H) ↔
          (x:G) ∈ (transfiniteFiltration p β : AddSubgroup G))
end LogicLineages.ModelsAlgebra.PGroups.Targets
