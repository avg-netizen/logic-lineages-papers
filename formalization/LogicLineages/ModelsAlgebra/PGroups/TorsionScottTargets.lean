module

public import LogicLineages.ModelsAlgebra.PGroups.ScottDefinitions
public import Mathlib.GroupTheory.Torsion

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.Targets

open GroupInfinitary
universe u v

/-- Actual torsion implies finiteness of every finitely generated subgroup;
no locally finite oracle is a premise. -/
def groupTorsionLocallyFinite : Prop :=
  ∀ (G : Type u) [AddCommGroup G], AddMonoid.IsTorsion G → LocallyFinite G

/-- The original p-primary condition implies actual finite additive order
of every element, with the original primality hypothesis retained. -/
def groupPPrimaryTorsion : Prop :=
  ∀ (p : ℕ), p.Prime → ∀ (G : Type u) [AddCommGroup G],
    (∀ x : G, ∃ k : ℕ, p ^ k • x = 0) → AddMonoid.IsTorsion G

/-- The paper01 Sigma_2 Scott obstruction specialized to the actual
countably infinite abelian p-groups. This is not the full classification. -/
def groupPPrimaryNoSigmaTwoScott : Prop :=
  ∀ (p : ℕ), p.Prime →
    ∀ (G : Type u) [AddCommGroup G] [Countable G] [Infinite G],
      (∀ x : G, ∃ k : ℕ, p ^ k • x = 0) →
        ∀ φ : Formula 0, Complexity .sigma (2 : Ordinal.{v}) φ →
          ¬ GroupScottSentence G φ

end LogicLineages.ModelsAlgebra.PGroups.Targets
