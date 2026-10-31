module
public import LogicLineages.ModelsAlgebra.PGroups.PPrimaryFiniteGenerationDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
universe u

def pPrimaryFiniteTupleExtension : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (p : ℕ), p ≠ 0 →
    (∀ x : G, ∃ k : ℕ, p^k • x = 0) →
    ∀ (B : AddSubgroup G) [Finite B] (n : ℕ) (d : Fin n → G),
      Finite ↥(B ⊔ AddSubgroup.closure (Set.range d))

def pPrimaryFiniteTupleClosure : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (p : ℕ), p ≠ 0 →
    (∀ x : G, ∃ k : ℕ, p^k • x = 0) →
    ∀ (n : ℕ) (d : Fin n → G), Finite (AddSubgroup.closure (Set.range d))

end LogicLineages.ModelsAlgebra.PGroups.Targets
