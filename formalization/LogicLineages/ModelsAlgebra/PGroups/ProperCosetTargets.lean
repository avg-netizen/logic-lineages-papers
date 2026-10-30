module
public import LogicLineages.ModelsAlgebra.PGroups.CoprimeFiltrationTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
universe u v

def groupProperCosetSumMembership : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (p : ℕ),
    (∀ x : G, ∃ n : ℕ, p ^ n • x = 0) →
    ∀ (B : AddSubgroup G) (x : G),
    (∀ b : B, ∀ α : Ordinal.{v},
      x + b ∈ (transfiniteFiltration p α : AddSubgroup G) →
      x ∈ (transfiniteFiltration p α : AddSubgroup G)) →
    ∀ z : ℤ, Nat.Coprime z.natAbs p → ∀ (b : B) (α : Ordinal.{v}),
      z • x + b ∈ (transfiniteFiltration p α : AddSubgroup G) ↔
      x ∈ (transfiniteFiltration p α : AddSubgroup G) ∧
      (b : G) ∈ (transfiniteFiltration p α : AddSubgroup G)

end LogicLineages.ModelsAlgebra.PGroups.Targets
