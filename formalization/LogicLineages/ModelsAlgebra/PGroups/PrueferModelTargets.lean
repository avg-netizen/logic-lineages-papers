module
public import LogicLineages.ModelsAlgebra.PGroups.PrueferModelDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets

def genuinePrueferModel : Prop :=
  ∀ (p : ℕ) [Fact p.Prime],
    (∀ x : PrueferModel p, ∃ k : ℕ, p^k • x = 0) ∧
    (∀ n : ℕ, n ≠ 0 → ∀ x : PrueferModel p, ∃ y : PrueferModel p, n • y = x) ∧
    (∃ t : PrueferModel p, t ≠ 0 ∧ p • t = 0)

end LogicLineages.ModelsAlgebra.PGroups.Targets
