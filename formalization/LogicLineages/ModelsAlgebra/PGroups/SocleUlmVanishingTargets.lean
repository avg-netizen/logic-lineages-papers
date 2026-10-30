module

public import LogicLineages.ModelsAlgebra.PGroups.SocleRootDefinitions
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.SetTheory.Ordinal.Arithmetic

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.Targets

open GroupInfinitary
universe u v

/-- Genuine cardinal rank zero of the actual quotient is equivalent to
collapse of the socle into its next filtration subgroup. -/
def groupUlmRankZeroSocle : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : Type u) [AddCommGroup G] (S : AddSubgroup G),
    Module.rank (ZMod p) (UlmLayer p S) = 0 ↔ pSocle p S ≤ pStep p S

/-- The source's zero-lower-invariants condition, derived by finite induction
on the actual decreasing filtration, not a cyclic classification assumption. -/
def groupSocleRootUlmVanishing : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : Type u) [AddCommGroup G] (j : ℕ),
    pSocle p (⊤ : AddSubgroup G) ≤ finiteFiltration p j ↔
      ∀ i : ℕ, i < j →
        Module.rank (ZMod p) (UlmLayer p (finiteFiltration p i : AddSubgroup G)) = 0

/-- The actual Pi_2 source clause characterizes vanishing of every lower
finite Ulm invariant. j=0 is included as a genuine vacuous case. -/
def groupSocleRootVanishingFormula : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (j n : ℕ),
    Complexity .pi (2 : Ordinal.{v}) (socleRootFormula p j n) ∧
      ∀ (G : Type u) [AddCommGroup G] (a : Fin n → G),
        (socleRootFormula p j n).Realize a ↔
          ∀ i : ℕ, i < j →
            Module.rank (ZMod p) (UlmLayer p (finiteFiltration p i : AddSubgroup G)) = 0

end LogicLineages.ModelsAlgebra.PGroups.Targets
