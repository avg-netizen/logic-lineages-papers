module
public import LogicLineages.ModelsAlgebra.PGroups.SocleCorrectionLinearTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
universe u v

def groupProperSocleTransport : Prop :=
  ∀ (G H : Type u) [AddCommGroup G] [AddCommGroup H] (p : ℕ) [Fact p.Prime]
    (B : AddSubgroup G) (C : AddSubgroup H) [Finite B] (f : B ≃+ C) (α : Ordinal.{v}),
    (∀ (b : B) (β : Ordinal.{v}), β ≤ α+1+1 →
      ((f b:H) ∈ (transfiniteFiltration p β : AddSubgroup H) ↔
        (b:G) ∈ (transfiniteFiltration p β : AddSubgroup G))) →
    Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α : AddSubgroup G)) ≤
      Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α : AddSubgroup H)) →
    ∀ a : G, a ∈ pSocle p (transfiniteFiltration p α) →
      a ∉ (transfiniteFiltration p (α+1) : AddSubgroup G) → a ∉ B →
      (∀ (b : B) (β : Ordinal.{v}), a+b ∈ (transfiniteFiltration p β : AddSubgroup G) →
        a ∈ (transfiniteFiltration p β : AddSubgroup G)) →
      ∃ w : H, w ∈ pSocle p (transfiniteFiltration p α) ∧
        w ∉ (transfiniteFiltration p (α+1) : AddSubgroup H) ∧ w ∉ C ∧
        ∀ (c : C) (β : Ordinal.{v}), w+c ∈ (transfiniteFiltration p β : AddSubgroup H) →
          w ∈ (transfiniteFiltration p β : AddSubgroup H)

end LogicLineages.ModelsAlgebra.PGroups.Targets
