module

public import LogicLineages.ModelsAlgebra.Differential.PolynomialCertificateSearchDefinitions

@[expose] public section

/-! The existing finite Euclidean verifier, returning its actual quotient and
remainder rather than just a divisibility bit. The zero denominator has the
explicit pair (0,a); all other inputs enumerate and verify standard finite
rational-polynomial certificates. Totality is a theorem, not an oracle. -/
namespace LogicLineages.ModelsAlgebra.Differential.PolynomialQuotientSearch

abbrev Input := PolynomialCertificateSearch.Input
abbrev Certificate := PolynomialCertificateSearch.Certificate

def atIndex (t : Input) (n : ℕ) : Option Certificate :=
  if DensePolynomial.isZero t.1 then some ([], t.2)
  else (Encodable.decode n : Option Certificate).bind fun w =>
    if PolynomialCertificateSearch.verify t.1 t.2 w then some w else none

def search (t : Input) : Part Certificate := Nat.rfindOpt (atIndex t)

end LogicLineages.ModelsAlgebra.Differential.PolynomialQuotientSearch
