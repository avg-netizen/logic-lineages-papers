module
public import LogicLineages.ModelsAlgebra.PGroups.IntrinsicNormalFormTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary

/-- The actual finite-short normal-form obstruction transported to intrinsic groups. -/
def groupIntrinsicNoPiTwoScott : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : Type) [AddCommGroup G] [Countable G] (k N : ℕ),
    0 < k → k ≤ N → (∀ g : G, p ^ N • g = 0) →
    Finite (multipleImage G (p ^ k)) → Infinite (multipleImage G (p ^ (k-1))) →
    (∀ j : ℕ, j < k-1 → Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j : AddSubgroup G)) < Cardinal.aleph0) →
    (∃ j : ℕ, j < k-1 ∧ Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j : AddSubgroup G)) ≠ 0) →
    ∀ φ : Formula 0, Complexity .pi (2 : Ordinal.{0}) φ → ¬ GroupScottSentence G φ

end LogicLineages.ModelsAlgebra.PGroups.Targets
