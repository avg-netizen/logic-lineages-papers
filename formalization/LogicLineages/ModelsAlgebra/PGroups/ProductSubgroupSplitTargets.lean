module
public import LogicLineages.ModelsAlgebra.PGroups.ProductSubgroupSplitDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
def productSubgroupSplit : Prop :=
  ∀ (G A B : Type) [AddCommGroup G] [AddCommGroup A] [AddCommGroup B]
    (S : AddSubgroup G) (e : S ≃+ A×B), ∃ K T : AddSubgroup G,
    S=K⊔T ∧ Disjoint K T ∧ Nonempty (K ≃+ A) ∧ Nonempty (T ≃+ B) ∧
    ∀ x : S, (x:G) ∈ K ↔ (e x).2=0
end LogicLineages.ModelsAlgebra.PGroups.Targets
