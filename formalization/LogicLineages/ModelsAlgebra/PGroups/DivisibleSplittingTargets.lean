module
public import LogicLineages.ModelsAlgebra.PGroups.DivisibleSplittingDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
/-- Divisibility produces a retraction, rather than assuming an extension or splitting oracle. -/
def divisibleSubgroupRetraction : Prop :=
  ∀ (G : Type) [AddCommGroup G] (D : AddSubgroup G), SubgroupDivisible D →
    ∃ r : G →+ D, SubgroupRetraction D r
/-- The literal maximal divisible subgroup has an actual reduced complement and coherent product. -/
def actualDivisibleSplitting : Prop :=
  ∀ (G : Type) [AddCommGroup G],
    ∃ (r : G →+ divisiblePart G) (R : AddSubgroup G),
      SubgroupRetraction (divisiblePart G) r ∧ R = r.ker ∧
      IsReducedAddGroup R ∧ Disjoint R (divisiblePart G) ∧ R ⊔ divisiblePart G = ⊤ ∧
      ∃ e : (R × divisiblePart G) ≃+ G, ∀ (x : R) (y : divisiblePart G),
        e (x,y) = (x:G) + y
end LogicLineages.ModelsAlgebra.PGroups.Targets
