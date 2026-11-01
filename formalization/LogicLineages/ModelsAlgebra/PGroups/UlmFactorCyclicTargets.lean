module
public import LogicLineages.ModelsAlgebra.PGroups.PrescribedTailDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.ZeroOmegaCyclicDefinitions
public import Mathlib.Data.Nat.Prime.Defs
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
/-- Every actual Ulm factor, including a possibly zero factor, has an
actual countable Sigma-cyclic presentation, not a specified-factor oracle. -/
def actualUlmFactorCyclicPresentation : Prop :=
  ∀ (p:ℕ) [Fact p.Prime] (G:Type) [AddCommGroup G] [Countable G],
    (∀x:G,∃k:ℕ,p^k • x=0) → ∀ξ:Ordinal.{0},
      ∃I:ℕ→Type,(∀n,Countable (I n)) ∧ Nonempty (UlmFactor p G ξ≃+ZeroOmegaCyclicSum p I)
/-- In an actual reduced primary group, a nonzero block-start subgroup
has a nontrivial actual quotient factor; no hidden finite-stage survival
or cyclic realization hypothesis is supplied. -/
def reducedUlmFactorNontrivial : Prop :=
  ∀ (p:ℕ) [Fact p.Prime] (G:Type) [AddCommGroup G] [Countable G],
    (∀x:G,∃k:ℕ,p^k • x=0) → IsReducedAddGroup G → ∀ξ:Ordinal.{0},
      (transfiniteFiltration p (Ordinal.omega0*ξ):AddSubgroup G)≠⊥ → Nontrivial (UlmFactor p G ξ)
end LogicLineages.ModelsAlgebra.PGroups.Targets
