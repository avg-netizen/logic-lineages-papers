module

public import LogicLineages.ModelsAlgebra.Differential.PolynomialCertificateSearchDefinitions
public import LogicLineages.ModelsAlgebra.Differential.CurveDefinitions

@[expose] public section

/-! Concrete input/output of the first-order decision. The input is a list of
Z-coefficients, each a finite Y-polynomial, plus the finite lower-order q.
The actual search tests r | r' q by finite Euclidean certificates, instead
of a factorization oracle for radical(r). Totality must be proved separately.
-/
namespace LogicLineages.ModelsAlgebra.Differential.OrderOneAlgorithm

abbrev Input := List DensePolynomial.Code

noncomputable def inputValue : Input → BivariatePolynomial
  | [] => 0
  | a :: as => Polynomial.C (DensePolynomial.value a) + Polynomial.X * inputValue as

def specialization (p : Input) : DensePolynomial.Code := p.getD 0 []

def search (p : Input) (q : DensePolynomial.Code) : Part Bool :=
  let r := specialization p
  if DensePolynomial.isZero r then Part.some false
  else PolynomialCertificateSearch.search (r, DensePolynomial.mul (DensePolynomial.derivative r) q)

end LogicLineages.ModelsAlgebra.Differential.OrderOneAlgorithm
