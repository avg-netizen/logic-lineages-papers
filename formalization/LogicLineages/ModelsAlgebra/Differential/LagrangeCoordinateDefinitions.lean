module

public import LogicLineages.ModelsAlgebra.Differential.LinearOperatorDefinitions
public import Mathlib.LinearAlgebra.Lagrange

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.LagrangeCoordinate

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

noncomputable def coordinate {n : ℕ} (D : Derivation K F F) (root : Fin n → K)
    (i : Fin n) (a : F) : F :=
  LinearOperator.applyOperator D (Lagrange.basis Finset.univ root i) a

end LogicLineages.ModelsAlgebra.Differential.LagrangeCoordinate
