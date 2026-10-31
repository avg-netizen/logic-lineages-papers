module
public import LogicLineages.ModelsAlgebra.PGroups.DivisibleNonisoDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
def divisibleInfiniteFiniteNoniso : Prop :=
  ∀ (R S D E : Type) [AddCommGroup R] [AddCommGroup S] [AddCommGroup D] [AddCommGroup E]
    (p : ℕ) [Infinite (pSocle p (⊤ : AddSubgroup D))]
    [Finite (pSocle p (⊤ : AddSubgroup E))],
    IsReducedAddGroup R → IsReducedAddGroup S → GroupDivisible D → GroupDivisible E →
    ¬ Nonempty ((R×D) ≃+ (S×E))
def divisibleFinitePrueferNoniso : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (R D : Type) [AddCommGroup R] [AddCommGroup D]
    [Finite (pSocle p (⊤ : AddSubgroup D))],
    IsReducedAddGroup R → GroupDivisible D →
    ¬ Nonempty ((R×D) ≃+ (R×(D×PrueferModel p)))
end LogicLineages.ModelsAlgebra.PGroups.Targets
