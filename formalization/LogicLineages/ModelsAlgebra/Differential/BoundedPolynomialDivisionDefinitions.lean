module

public import LogicLineages.ModelsAlgebra.Differential.BoxPolynomialCodeDefinitions
public import LogicLineages.ModelsAlgebra.Differential.PolynomialQuotientSearchDefinitions

@[expose] public section

/-! A totalizable multivariate divisibility algorithm. The ordinary univariate
division supplies a candidate quotient. Its multivariate interpretation is then
checked at twice the input base to prevent carries from aliasing products. -/
namespace LogicLineages.ModelsAlgebra.Differential.BoundedPolynomialDivision

abbrev Input := ℕ × ℕ × BoxPolynomialCode.Code × BoxPolynomialCode.Code

def prepare (t : Input) : PolynomialQuotientSearch.Input :=
  (BoxPolynomialCode.rebase t.1 t.2.1 t.2.1 t.2.2.1,
    BoxPolynomialCode.rebase t.1 t.2.1 t.2.1 t.2.2.2)

def verify (t : Input) (w : PolynomialQuotientSearch.Certificate) : Bool :=
  DensePolynomial.isZero w.2 && PolynomialCertificateSearch.equal
    (DensePolynomial.mul
      (BoxPolynomialCode.rebase t.1 t.2.1 (2 * t.2.1) t.2.2.1)
      (BoxPolynomialCode.rebase t.1 t.2.1 (2 * t.2.1) w.1))
    (BoxPolynomialCode.rebase t.1 t.2.1 (2 * t.2.1) t.2.2.2)

def search (t : Input) : Part Bool := (PolynomialQuotientSearch.search (prepare t)).map (verify t)

end LogicLineages.ModelsAlgebra.Differential.BoundedPolynomialDivision
