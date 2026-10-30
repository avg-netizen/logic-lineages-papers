module

public import LogicLineages.ModelsAlgebra.PGroups.UpperCyclicDefinitions

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary

def groupUpperCyclicFinite : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (s : ℕ) (r : Fin s → ℕ), Finite (UpperCyclicGroup p s r)

def groupUpperCyclicAnnihilation : Prop :=
  ∀ (p s N : ℕ) (r : Fin s → ℕ), (∀ a, r a ≤ N) →
    ∀ x : UpperCyclicGroup p s r, p ^ N • x = 0

/-- Actual roots are obtained from deeper cyclic roots, not supplied by a
property of the finite upper factor. The source r>k is a specialization. -/
def groupUpperCyclicSocleRoots : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (k s : ℕ), 0 < k →
    ∀ (r : Fin s → ℕ), (∀ a, k ≤ r a) → ∀ x : UpperCyclicGroup p s r,
      p • x = 0 → ∃ y : UpperCyclicGroup p s r, p ^ (k - 1) • y = x

end LogicLineages.ModelsAlgebra.PGroups.Targets
