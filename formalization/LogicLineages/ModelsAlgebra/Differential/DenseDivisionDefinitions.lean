module

public import LogicLineages.ModelsAlgebra.Differential.DensePolynomialDefinitions

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.DenseDivision

open DensePolynomial

/-- A bounded scan for the highest nonzero coefficient; zero has degree zero.
This is the actual finite search, not a call to abstract polynomial degree. -/
def degree (a : Code) : ℕ :=
  (a.length - 1).findGreatest (fun i => RationalCode.isZero (a.getD i RationalCode.zero) = false)
def leading (a : Code) : RationalCode.Code := a.getD (degree a) RationalCode.zero
def shift (n : ℕ) (a : Code) : Code := List.replicate n RationalCode.zero ++ a

/-- Cancel the coefficient in degree `degree b + k`. Descending fixed indices
avoid a dynamic remainder degree or an unbounded termination search. -/
def step (b : Code) (k : ℕ) (r : Code) : Code :=
  if DensePolynomial.isZero b then r
  else DensePolynomial.add r (DensePolynomial.neg
    (shift k (DensePolynomial.scale
      (RationalCode.div (r.getD (degree b + k) RationalCode.zero) (leading b)) b)))

/-- The fixed descending list includes every potentially nonzero coefficient
above the divisor degree. Cancellations at already-zero coefficients are inert. -/
def remainder (b a : Code) : Code :=
  (List.range a.length).reverse.foldl (fun r k => step b k r) a

def divides (b a : Code) : Bool := DensePolynomial.isZero (remainder b a)

end LogicLineages.ModelsAlgebra.Differential.DenseDivision
