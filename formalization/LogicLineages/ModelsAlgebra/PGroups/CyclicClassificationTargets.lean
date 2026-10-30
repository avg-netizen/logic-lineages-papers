module
public import LogicLineages.ModelsAlgebra.PGroups.CyclicDecompositionTargets
public import Mathlib.LinearAlgebra.Dimension.Basic
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary

/-- Actual quotient bases calibrate the indices in a genuine decomposition. -/
def groupBoundedCyclicCalibratedDecomposition : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : Type) [AddCommGroup G] (N : ℕ),
    (∀ g : G, p ^ N • g = 0) →
      ∃ I : Fin N → Type, Nonempty (G ≃+ CyclicRootSum p N I) ∧
        ∀ l : Fin N, Cardinal.mk (I l) =
          Module.rank (ZMod p) (UlmLayer p (finiteFiltration p l.val : AddSubgroup G))

/-- Actual coordinate reindexing, not an invariant correctness premise. -/
def groupCyclicRootSumReindex : Prop :=
  ∀ (p N : ℕ) (I J : Fin N → Type),
    (∀ l : Fin N, Nonempty (I l ≃ J l)) →
      Nonempty (CyclicRootSum p N I ≃+ CyclicRootSum p N J)

end LogicLineages.ModelsAlgebra.PGroups.Targets
