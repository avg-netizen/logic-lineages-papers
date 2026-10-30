module
public import LogicLineages.ModelsAlgebra.PGroups.CyclicDirectSumDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.AdaptedSocleDefinitions
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary

def groupCyclicRootSumSingle : Prop := by
  classical
  exact
    ∀ (p N : ℕ) (I : Fin N → Type) (G : Type) [AddCommGroup G]
      (y : ∀ l : Fin N, I l → G) (hy : ∀ l i, p ^ (l.val+1) • y l i = 0)
      (a : Σ l : Fin N, I l) (z : ZMod (p ^ (a.1.val+1))),
      cyclicRootSumHom p N I G y hy (DFinsupp.single a z) =
        cyclicRootHom (p ^ (a.1.val+1)) G (y a.1 a.2) (hy a.1 a.2) z

def groupCyclicRootSumExponent : Prop :=
  ∀ (p N : ℕ) (I : Fin N → Type) (z : CyclicRootSum p N I), p ^ N • z = 0

def groupCyclicSocleCoefficientsInjective : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N : ℕ) (I : Fin N → Type),
    Function.Injective (cyclicSocleCoefficients p N I)

def groupCyclicSocleCoefficientsRange : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N : ℕ) (I : Fin N → Type),
    (cyclicSocleCoefficients p N I).range =
      (nsmulAddMonoidHom p : CyclicRootSum p N I →+ CyclicRootSum p N I).ker

/-- Literal map coherence with the existing canonical socle scalar action. -/
def groupCyclicRootSumSocleComposition : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N : ℕ) (I : Fin N → Type) (G : Type) [AddCommGroup G]
    (y : ∀ l : Fin N, I l → G) (hy : ∀ l i, p ^ (l.val+1) • y l i = 0)
    (v : (Σ l : Fin N, I l) → pSocle p (⊤ : AddSubgroup G)),
    (∀ a : Σ l : Fin N, I l, p ^ a.1.val • y a.1 a.2 = (v a : G)) →
    ∀ c : (Σ l : Fin N, I l) →₀ ZMod p,
      cyclicRootSumHom p N I G y hy (cyclicSocleCoefficients p N I c) =
        ((Finsupp.linearCombination (ZMod p) v c : pSocle p (⊤ : AddSubgroup G)) : G)

end LogicLineages.ModelsAlgebra.PGroups.Targets
