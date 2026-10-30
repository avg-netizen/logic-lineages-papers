module
public import LogicLineages.ModelsAlgebra.PGroups.TransfiniteFiltration
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Data.Nat.Prime.Defs
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
universe u v

def groupSuccessorSuitableRoot : Prop :=
  ∀ (G H : Type u) [AddCommGroup G] [AddCommGroup H] (p : ℕ) [Fact p.Prime]
    (B : AddSubgroup G) (x : G) (α : Ordinal.{v}), x ∉ B → ∀ hpx : p • x ∈ B,
    ∀ (f : B →+ H), Function.Injective f →
    (∀ (b : B) (β : Ordinal.{v}), β ≤ α + 1 + 1 →
      (f b ∈ (transfiniteFiltration p β : AddSubgroup H) ↔
        (b : G) ∈ (transfiniteFiltration p β : AddSubgroup G))) →
    x ∈ (transfiniteFiltration p α : AddSubgroup G) →
    x ∉ (transfiniteFiltration p (α + 1) : AddSubgroup G) →
    p • x ∈ (transfiniteFiltration p (α + 1) : AddSubgroup G) →
    p • x ∉ (transfiniteFiltration p (α + 1 + 1) : AddSubgroup G) →
    (∀ b : B, ∀ β : Ordinal.{v},
      x + b ∈ (transfiniteFiltration p β : AddSubgroup G) →
      x ∈ (transfiniteFiltration p β : AddSubgroup G)) →
    (∀ b : B,
      (∀ c : B, ∀ β : Ordinal.{v},
        x + c ∈ (transfiniteFiltration p β : AddSubgroup G) →
        x + b ∈ (transfiniteFiltration p β : AddSubgroup G)) →
      ∀ β : Ordinal.{v}, p • (x + b) ∈ (transfiniteFiltration p β : AddSubgroup G) →
        p • x ∈ (transfiniteFiltration p β : AddSubgroup G)) →
    ∃ w : H, p • w = f ⟨p • x,hpx⟩ ∧
      w ∈ (transfiniteFiltration p α : AddSubgroup H) ∧
      w ∉ (transfiniteFiltration p (α + 1) : AddSubgroup H) ∧ w ∉ f.range ∧
      ∀ (b : B) (β : Ordinal.{v}),
        w + f b ∈ (transfiniteFiltration p β : AddSubgroup H) →
        w ∈ (transfiniteFiltration p β : AddSubgroup H)

end LogicLineages.ModelsAlgebra.PGroups.Targets
