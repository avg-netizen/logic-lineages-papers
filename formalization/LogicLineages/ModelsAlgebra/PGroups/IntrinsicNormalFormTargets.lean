module
public import LogicLineages.ModelsAlgebra.PGroups.IntrinsicBoundedScottTargets
public import LogicLineages.ModelsAlgebra.PGroups.FullShiftDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary

/-- Actual normal-form existence; no decomposition correctness input is permitted. -/
def groupIntrinsicFullShiftNormalForm : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : Type) [AddCommGroup G] [Countable G] (k N : ℕ),
    0 < k → k ≤ N → (∀ g : G, p ^ N • g = 0) →
    Finite (multipleImage G (p ^ k)) → Infinite (multipleImage G (p ^ (k-1))) →
    (∀ j : ℕ, j < k-1 → Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j : AddSubgroup G)) < Cardinal.aleph0) →
    ∃ (t : ℕ) (ell : Fin t → ℕ) (s : ℕ) (r : Fin s → ℕ),
      (∀ a, 0 < ell a ∧ ell a < k) ∧ (∀ a, k < r a ∧ r a ≤ N) ∧
      Nonempty (G ≃+ FullShiftGroup p k t ell s r)

/-- A genuine nonzero lower invariant forces an actual short block. -/
def groupNonzeroLowerShortBlock : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : Type) [AddCommGroup G] (k t s : ℕ)
    (ell : Fin t → ℕ) (r : Fin s → ℕ),
    (∀ a, ell a < k) → (∀ a, k < r a) →
    Nonempty (G ≃+ FullShiftGroup p k t ell s r) →
    (∃ j : ℕ, j < k-1 ∧ Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j : AddSubgroup G)) ≠ 0) →
    0 < t

end LogicLineages.ModelsAlgebra.PGroups.Targets
