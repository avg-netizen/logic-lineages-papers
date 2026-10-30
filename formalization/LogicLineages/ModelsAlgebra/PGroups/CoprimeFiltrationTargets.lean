module
public import LogicLineages.ModelsAlgebra.PGroups.TransfiniteFiltration
public import Mathlib.Data.Nat.GCD.Basic
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
universe u v

def groupCoprimeSubgroupMembership : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (p : ℕ),
    (∀ x : G, ∃ n : ℕ, p ^ n • x = 0) →
    ∀ (S : AddSubgroup G) (z : ℤ), Nat.Coprime z.natAbs p →
      ∀ x : G, z • x ∈ S ↔ x ∈ S

def groupCoprimeFiltrationMembership : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (p : ℕ),
    (∀ x : G, ∃ n : ℕ, p ^ n • x = 0) →
    ∀ (z : ℤ), Nat.Coprime z.natAbs p → ∀ (x : G) (α : Ordinal.{v}),
      z • x ∈ (transfiniteFiltration p α : AddSubgroup G) ↔
      x ∈ (transfiniteFiltration p α : AddSubgroup G)

end LogicLineages.ModelsAlgebra.PGroups.Targets
