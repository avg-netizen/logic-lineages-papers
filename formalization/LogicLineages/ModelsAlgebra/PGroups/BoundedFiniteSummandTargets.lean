module
public import LogicLineages.ModelsAlgebra.PGroups.BoundedFiniteSummandDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
def boundedFiniteSummand : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : Type) [AddCommGroup G] (N : ℕ),
    (∀ x : G, p^N • x=0) → ∀ (B : AddSubgroup G) [Finite B] (x : G),
    ∃ K T : AddSubgroup G, Finite K ∧ B ≤ K ∧ x ∈ K ∧ Disjoint K T ∧ K ⊔ T = ⊤
end LogicLineages.ModelsAlgebra.PGroups.Targets
