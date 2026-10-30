module

public import LogicLineages.ModelsAlgebra.Differential.SpectralResultantDefinitions
public import LogicLineages.ModelsAlgebra.Differential.NumericDeterminantDefinitions
public import LogicLineages.ModelsAlgebra.Differential.BoxPolynomialCodeDefinitions
public import LogicLineages.ModelsAlgebra.Differential.OrderOneAlgorithmDefinitions

@[expose] public section

/-! Concrete rational operations computing the source Sylvester determinant
after bounded Kronecker substitution. Outer coefficients are the already
defined dense rational-polynomial codes; no roots or splitting-field elements
occur among the input data. Every matrix entry and summand is finite code. -/
namespace LogicLineages.ModelsAlgebra.Differential.SpectralResultantCode

abbrev OuterCode := List DensePolynomial.Code

noncomputable def outerValue (p : OuterCode) : Polynomial (Polynomial ℚ) :=
  OrderOneAlgorithm.inputValue p

def outerAdd (a b : OuterCode) : OuterCode :=
  (List.range (max a.length b.length)).map fun i =>
    DensePolynomial.add (a.getD i []) (b.getD i [])

def outerMonomial (a : DensePolynomial.Code) (k : ℕ) : OuterCode :=
  List.replicate k [] ++ [a]

def generating (n B : ℕ) (fc : DensePolynomial.Code) : OuterCode :=
  (List.range n).foldr (fun k acc =>
    (List.range (n + 1)).foldr (fun j inner =>
      if k + 1 ≤ j then outerAdd
        (outerMonomial (BoxPolynomialCode.monomial (fc.getD j RationalCode.zero) (B ^ k))
          (j - (k + 1))) inner else inner) acc) []

def sylvesterEntry (n B : ℕ) (fc : DensePolynomial.Code) (i j : ℕ) : DensePolynomial.Code :=
  if j < n then
    if j ≤ i ∧ i ≤ j + (n - 1) then (generating n B fc).getD (i - j) [] else []
  else
    if j - n ≤ i ∧ i ≤ (j - n) + n then [fc.getD (i - (j - n)) RationalCode.zero] else []

def matrix (n B : ℕ) (fc : DensePolynomial.Code) : NumericDeterminant.MatrixCode :=
  let d := n + (n - 1)
  (List.range (d * d)).map fun k => sylvesterEntry n B fc (k / d) (k % d)

def obstruction (n B : ℕ) (fc : DensePolynomial.Code) : DensePolynomial.Code :=
  NumericDeterminant.determinant (n + (n - 1)) (matrix n B fc)

end LogicLineages.ModelsAlgebra.Differential.SpectralResultantCode
