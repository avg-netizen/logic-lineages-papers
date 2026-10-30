module

public import LogicLineages.ModelsAlgebra.Differential.NumericDeterminantDefinitions

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.Targets

def numericDeterminantPermutationWeight : Prop := ∀ n (σ : Equiv.Perm (Fin n)),
  RationalCode.value (NumericDeterminant.weight n
    (KroneckerIndex.index (n + 2) (fun i : Fin n => (σ i).val))) = (σ.sign : ℤ)

def numericDeterminantCorrect : Prop := ∀ n (m : NumericDeterminant.MatrixCode),
  DensePolynomial.value (NumericDeterminant.determinant n m) =
    (NumericDeterminant.value n m).det

def numericDeterminantPrimitiveRecursive : Prop :=
  Primrec₂ NumericDeterminant.determinant

end LogicLineages.ModelsAlgebra.Differential.Targets
