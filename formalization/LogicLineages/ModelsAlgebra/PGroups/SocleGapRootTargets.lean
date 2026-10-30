module
public import LogicLineages.ModelsAlgebra.PGroups.ProperSocleTransportTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
universe u v

def groupSocleGapSuitableRoot : Prop :=
  ∀ (G H : Type u) [AddCommGroup G] [AddCommGroup H] (p : ℕ) [Fact p.Prime]
    (B : AddSubgroup G) (C : AddSubgroup H) [Finite B] (x : G) (α : Ordinal.{v}),
    x ∉ B → ∀ hpx : p • x ∈ B, ∀ f : B ≃+ C,
    (∀ (b : B) (β : Ordinal.{v}), β ≤ α+1+1 →
      ((f b:H) ∈ (transfiniteFiltration p β : AddSubgroup H) ↔
        (b:G) ∈ (transfiniteFiltration p β : AddSubgroup G))) →
    Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α : AddSubgroup G)) ≤
      Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α : AddSubgroup H)) →
    x ∈ (transfiniteFiltration p α : AddSubgroup G) →
    x ∉ (transfiniteFiltration p (α+1) : AddSubgroup G) →
    p • x ∈ (transfiniteFiltration p (α+1+1) : AddSubgroup G) →
    (∀ (b : B) (β : Ordinal.{v}), x+b ∈ (transfiniteFiltration p β : AddSubgroup G) →
      x ∈ (transfiniteFiltration p β : AddSubgroup G)) →
    ∃ w : H, p • w = (f ⟨p • x,hpx⟩:H) ∧
      w ∈ (transfiniteFiltration p α : AddSubgroup H) ∧
      w ∉ (transfiniteFiltration p (α+1) : AddSubgroup H) ∧ w ∉ C ∧
      ∀ (c : C) (β : Ordinal.{v}), w+c ∈ (transfiniteFiltration p β : AddSubgroup H) →
        w ∈ (transfiniteFiltration p β : AddSubgroup H)

end LogicLineages.ModelsAlgebra.PGroups.Targets
