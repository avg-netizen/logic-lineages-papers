module
public import LogicLineages.ModelsAlgebra.PGroups.AdaptedSocleDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.TransfiniteDefinitions
public import Mathlib.LinearAlgebra.Dimension.Basic
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
/-- Literal divisibility of an additive subgroup. -/
def SubgroupDivisible {G : Type} [AddCommGroup G] (S : AddSubgroup G) : Prop :=
  ∀ n : ℕ, n ≠ 0 → ∀ x : S, ∃ y : S, n • y = x
/-- The supremum of all actual divisible subgroups, without a splitting oracle. -/
noncomputable def divisiblePart (G : Type) [AddCommGroup G] : AddSubgroup G :=
  ⨆ S : {S : AddSubgroup G // SubgroupDivisible S}, S.val
/-- Actual dimension of the p-socle of the maximal divisible subgroup.
The connection to a Prüfer summand decomposition is a separate obligation. -/
noncomputable def divisibleSocleRank (p : ℕ) (G : Type) [AddCommGroup G] : Cardinal :=
  Module.rank (ZMod p) (pSocle p (divisiblePart G))
end LogicLineages.ModelsAlgebra.PGroups
