module

public import LogicLineages.ModelsAlgebra.Differential.DensePolynomialDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section

/-! A finite quotient/remainder verifier and an actual partial-recursive search
for rational-polynomial divisibility. Verification uses only the explicit code
arithmetic. Euclidean witness existence/totality are obligations in the targets;
an effective division algorithm is neither assumed nor built into the data.
-/
namespace LogicLineages.ModelsAlgebra.Differential.PolynomialCertificateSearch

open DensePolynomial
abbrev Input := Code × Code
abbrev Certificate := Code × Code

def degree (a : Code) : ℕ :=
  (a.length - 1).findGreatest (fun i => RationalCode.isZero (a.getD i RationalCode.zero) = false)

def equal (a b : Code) : Bool :=
  DensePolynomial.isZero (DensePolynomial.add a (DensePolynomial.neg b))

def verify (b a : Code) (w : Certificate) : Bool :=
  equal a (DensePolynomial.add (DensePolynomial.mul b w.1) w.2) &&
    (DensePolynomial.isZero w.2 || decide (degree w.2 < degree b))

/-- The zero-divisor branch returns the exact test `0 | a ↔ a=0` directly.
Otherwise every standard-coded quotient/remainder candidate is eventually
visited, and malformed codes cannot produce an answer. -/
def atIndex (t : Input) (n : ℕ) : Option Bool :=
  if DensePolynomial.isZero t.1 then some (DensePolynomial.isZero t.2)
  else (Encodable.decode n : Option Certificate).bind fun w =>
    if verify t.1 t.2 w then some (DensePolynomial.isZero w.2) else none

def search (t : Input) : Part Bool := Nat.rfindOpt (atIndex t)

end LogicLineages.ModelsAlgebra.Differential.PolynomialCertificateSearch
