module

public import LogicLineages.ModelsAlgebra.Differential.HyperplaneDefinitions

@[expose] public section

/-! Exact hyperplane-restriction suppliers in paper 15 thm:spectral negative
branch. A missing coordinate is derived from failure of product divisibility,
not assumed as an oracle. -/
namespace LogicLineages.ModelsAlgebra.Differential.Targets

universe u v

def coordinateRestrictionKernel : Prop :=
  ∀ (K : Type u) (ι : Type v) [Field K] [DecidableEq ι]
    (i : ι) (q : MvPolynomial ι K),
    MvPolynomial.X i ∣ q ↔ Hyperplane.restrictZero i q = 0

def coordinateProductMissingWitness : Prop :=
  ∀ (K : Type u) (n : ℕ) [Field K] (q : MvPolynomial (Fin n) K),
    (¬ (∏ i : Fin n, MvPolynomial.X i) ∣ q) ↔
      ∃ i : Fin n, Hyperplane.restrictZero i q ≠ 0

end LogicLineages.ModelsAlgebra.Differential.Targets
