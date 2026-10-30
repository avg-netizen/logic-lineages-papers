module
public import LogicLineages.ModelsAlgebra.PGroups.CyclicDirectSumTargets
public import LogicLineages.ModelsAlgebra.PGroups.RootGenerationTargets
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary

/-- Injection is derived from actual socle independence, not assumed on the cyclic map. -/
def groupCyclicRootSumInjective : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N : ℕ) (I : Fin N → Type) (G : Type) [AddCommGroup G]
    (y : ∀ l : Fin N, I l → G) (hy : ∀ l i, p ^ (l.val+1) • y l i = 0)
    (v : (Σ l : Fin N, I l) → pSocle p (⊤ : AddSubgroup G)),
    (∀ a : Σ l : Fin N, I l, p ^ a.1.val • y a.1 a.2 = (v a : G)) →
    LinearIndependent (ZMod p) v → Function.Injective (cyclicRootSumHom p N I G y hy)

/-- Actual quotient bases and roots imply the literal map is onto. -/
def groupCyclicRootSumSurjective : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : Type) [AddCommGroup G] (N : ℕ),
    (∀ g : G, p ^ N • g = 0) → ∀ (I : Fin N → Type)
    (b : ∀ l : Fin N, Module.Basis (I l) (ZMod p) (UlmLayer p (finiteFiltration p l.val : AddSubgroup G)))
    (x : ∀ l : Fin N, I l → pSocle p (finiteFiltration p l.val : AddSubgroup G))
    (y : ∀ l : Fin N, I l → G) (hy : ∀ l i, p ^ (l.val+1) • y l i = 0),
    (∀ l i, QuotientAddGroup.mk' (successorSocleSubgroup p (finiteFiltration p l.val)) (x l i) = b l i) →
    (∀ l i, p ^ l.val • y l i = (x l i : G)) →
      Function.Surjective (cyclicRootSumHom p N I G y hy)

/-- Genuine bounded cyclic decomposition existence, with no supplied classification data. -/
def groupBoundedCyclicDecomposition : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : Type) [AddCommGroup G] (N : ℕ),
    (∀ g : G, p ^ N • g = 0) →
      ∃ I : Fin N → Type, Nonempty (G ≃+ CyclicRootSum p N I)

end LogicLineages.ModelsAlgebra.PGroups.Targets
