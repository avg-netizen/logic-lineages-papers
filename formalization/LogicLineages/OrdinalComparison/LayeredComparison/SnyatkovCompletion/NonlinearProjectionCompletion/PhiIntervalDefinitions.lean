module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.DominantBoundaryDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PhiInterval

/-- Exact least original input satisfying the signed domain and scaled-Phi
lower bound. The initial argument of the ORIGINAL signed domain is handled
before the old positive floor-inverse crossing is used. -/
def lowerBound (a : Nat) (shift : Int) (target : Nat) : Nat :=
  if target ≤ a * Phi shift.toNat then (-shift).toNat
  else ((DominantBoundary.positiveCrossing a target : Int) - shift).toNat

def crossingTerm (a : Nat) (lower : Term) : Term :=
  .add (.phiInverse (.divide a (.subtract lower (.numeral 1)))) (.numeral 1)
def initialGuard (a : Nat) (shift : Int) (lower : Term) : Matrix :=
  atMost lower (.multiply a (.phi (.numeral shift.toNat)))
def initialStart (shift : Int) : Term := .numeral (-shift).toNat
def tailStart (a : Nat) (shift : Int) (lower : Term) : Term :=
  shiftTerm (crossingTerm a lower) (-shift)

/-- Literal natural remainder using the existing expanded arithmetic signature. -/
def residueTerm (m : Nat) (t : Term) : Term :=
  .subtract t (.multiply m (.divide m t))

def interval (i a : Nat) (shift : Int) (m : Nat) (lower upper residue : Term) : Matrix :=
  let value := Term.multiply a (.phi (shiftTerm (.variable i) shift))
  .conjunction (shiftDomain (.variable i) shift)
    (.conjunction (atMost lower value)
      (.conjunction (atMost value upper)
        (.equal (residueTerm m (.variable i)) (residueTerm m residue))))

/-- A finite compiler whose number of branches is the actual modulus.
Every original condition, including the congruence and signed domain, is
retained in every branch. -/
def fromStart (i a : Nat) (shift : Int) (m : Nat) (lower upper residue start : Term) : Matrix :=
  Matrix.any ((List.range m).map (fun d =>
    (interval i a shift m lower upper residue).substitute i (.add start (.numeral d))))

def project (i a : Nat) (shift : Int) (m : Nat) (lower upper residue : Term) : Matrix :=
  .disjunction
    (.conjunction (initialGuard a shift lower)
      (fromStart i a shift m lower upper residue (initialStart shift)))
    (.conjunction (.negative (initialGuard a shift lower))
      (fromStart i a shift m lower upper residue (tailStart a shift lower)))

namespace Code
def divide (m t : Nat) : Nat := 10 * Nat.pair m t + 5
def crossingTerm (a lower : Nat) : Nat :=
  WindowCode.add
    (DominantBoundary.Code.inverse (divide a (WindowCode.subtract lower (WindowCode.numeral 1))))
    (WindowCode.numeral 1)
def initialGuard (a : Nat) (shift : Int) (lower : Nat) : Nat :=
  WindowCode.atMost lower (WindowCode.multiply a (WindowCode.phi (WindowCode.numeral shift.toNat)))
def initialStart (shift : Int) : Nat := WindowCode.numeral (-shift).toNat
def tailStart (a : Nat) (shift : Int) (lower : Nat) : Nat :=
  WindowCode.shift (crossingTerm a lower) (-shift)
def residueTerm (m t : Nat) : Nat := WindowCode.subtract t (WindowCode.multiply m (divide m t))
def interval (i a : Nat) (shift : Int) (m lower upper residue : Nat) : Nat :=
  let value := WindowCode.multiply a (WindowCode.phi (WindowCode.shift (WindowCode.var i) shift))
  WindowCode.conjunction (WindowCode.domain (WindowCode.var i) shift)
    (WindowCode.conjunction (WindowCode.atMost lower value)
      (WindowCode.conjunction (WindowCode.atMost value upper)
        (8 * Nat.pair (residueTerm m (WindowCode.var i)) (residueTerm m residue) + 2)))
def fromStart (i a : Nat) (shift : Int) (m lower upper residue start : Nat) : Nat :=
  WindowCode.any ((List.range m).map (fun d =>
    WindowCode.matrixSubstitute i (WindowCode.add start (WindowCode.numeral d))
      (interval i a shift m lower upper residue)))

abbrev Input := Nat × (Nat × (Int × (Nat × (Nat × (Nat × Nat)))))
def project (q : Input) : Nat :=
  WindowCode.disjunction
    (WindowCode.conjunction (initialGuard q.2.1 q.2.2.1 q.2.2.2.2.1)
      (fromStart q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2.1
        q.2.2.2.2.2.2 (initialStart q.2.2.1)))
    (WindowCode.conjunction (WindowCode.negative (initialGuard q.2.1 q.2.2.1 q.2.2.2.2.1))
      (fromStart q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2.1
        q.2.2.2.2.2.2 (tailStart q.2.1 q.2.2.1 q.2.2.2.2.1)))
end Code

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PhiInterval
