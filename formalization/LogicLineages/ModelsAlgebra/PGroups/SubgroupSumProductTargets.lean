module
public import LogicLineages.ModelsAlgebra.PGroups.SubgroupSumProductDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
def subgroupSumProduct : Prop :=
  ∀ (G : Type) [AddCommGroup G] (S K T : AddSubgroup G), S=K⊔T → Disjoint K T →
    ∃ e : (K × T) ≃+ S, ∀ (x : K) (y : T), (e (x,y):G) = (x:G)+y
end LogicLineages.ModelsAlgebra.PGroups.Targets
