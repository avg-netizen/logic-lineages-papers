module
public import LogicLineages.ModelsAlgebra.PGroups.AtomicGeneratedIsoDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupBackAndForth
universe u

def atomicGeneratedIso : Prop :=
  ∀ (G H : Type u) [AddCommGroup G] [AddCommGroup H] (n : ℕ)
    (a : Fin n → G) (b : Fin n → H),
    AtomicAgreement a b ↔
      ∃ e : AddSubgroup.closure (Set.range a) ≃+ AddSubgroup.closure (Set.range b),
        ∀ i, (e ⟨a i,AddSubgroup.subset_closure ⟨i,rfl⟩⟩ : H) = b i
end LogicLineages.ModelsAlgebra.PGroups.Targets
