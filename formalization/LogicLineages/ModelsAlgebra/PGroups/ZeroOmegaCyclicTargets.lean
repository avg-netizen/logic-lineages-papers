module
public import LogicLineages.ModelsAlgebra.PGroups.ZeroOmegaCyclicDefinitions
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.LinearAlgebra.Dimension.Basic
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
/-- Literal countable cyclic sum: actual nature, actual zero omega stage,
and exact finite-stage Ulm ranks. -/
def zeroOmegaCyclicSumCalibration : Prop :=
  ∀ (p:ℕ) [Fact p.Prime] (I:ℕ→Type) [∀n,Countable (I n)],
    Countable (ZeroOmegaCyclicSum p I) ∧
    (∀x:ZeroOmegaCyclicSum p I,∃k:ℕ,p^k • x=0) ∧
    (transfiniteFiltration p (Ordinal.omega0:Ordinal.{0}):AddSubgroup (ZeroOmegaCyclicSum p I))=⊥ ∧
    ∀n:ℕ,Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p (n:Ordinal.{0}):AddSubgroup (ZeroOmegaCyclicSum p I)))=
      Cardinal.mk (I n)
/-- Actual Sigma-cyclic presentation of EVERY countable primary group
with zero omega stage. The cardinal-calibrated actual summands and an
actual additive isomorphism are conclusions, not a realization promise. -/
def countableZeroOmegaCyclicDecomposition : Prop :=
  ∀ (p:ℕ) [Fact p.Prime] (G:Type) [AddCommGroup G] [Countable G],
    (∀x:G,∃k:ℕ,p^k • x=0) →
    (transfiniteFiltration p (Ordinal.omega0:Ordinal.{0}):AddSubgroup G)=⊥ →
    ∃I:ℕ→Type,(∀n,Countable (I n)) ∧ Nonempty (G≃+ZeroOmegaCyclicSum p I) ∧
      ∀n:ℕ,Cardinal.mk (I n)=Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p (n:Ordinal.{0}):AddSubgroup G))
end LogicLineages.ModelsAlgebra.PGroups.Targets
