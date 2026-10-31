module
public import LogicLineages.ModelsAlgebra.PGroups.WalkerGroupNatureDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets

def walkerCountableSuccessor : Prop :=
  ∀ ξ : Ordinal.{0}, ∀ [Countable ξ.ToType], Countable (ξ+1).ToType

/-- The source proof's actual countable reduced Abelian p-group property,
including p-primary torsion and absence of nonzero divisible subgroups. -/
def walkerSourceGroupNature : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], ∀ ξ : Ordinal.{0}, ∀ [Countable ξ.ToType],
    Countable (WalkerSourceGroup p ξ) ∧
    (∀ x : WalkerSourceGroup p ξ, ∃ n : ℕ, p^n • x = 0) ∧
    (∀ S : AddSubgroup (WalkerSourceGroup p ξ),
      (∀ n : ℕ, n ≠ 0 → ∀ x : S, ∃ y : S, n • y = x) → S = ⊥)

end LogicLineages.ModelsAlgebra.PGroups.Targets
