module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.HyperWindowCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearWindow

/-- false selects Phi(n+e); true selects Phi(H(n+e)+h). The outer shift h
is source data only for the true constructor, where its domain is retained. -/
def valueTerm (i : Nat) (kind : Bool) (e h : Int) : Term :=
  if kind then HyperWindow.valueTerm i e h else .phi (shiftTerm (.variable i) e)
def domainMatrix (i : Nat) (kind : Bool) (e h : Int) : Matrix :=
  if kind then HyperWindow.domainMatrix i e h else shiftDomain (.variable i) e

def shiftBudget (kind : Bool) (e h : Int) : Nat :=
  e.natAbs + if kind then h.natAbs else 0

/-- Literal quantitative source remarks/casesII3--4. This bound follows from
the actual Phi quadratic lower bound and actual H(n)>=n+1, not an oracle. -/
def bound (kind : Bool) (e h : Int) (a : Nat) : Nat :=
  a + a * shiftBudget kind e h + shiftBudget kind e h + 1

/-- The active nonlinear occurrence of the LINEAR variable j is explicitly
retained. Source maximal-summand guards supply active(j)<=leading(i); original
coefficient normalization supplies leading(i)<=a*j. Both domains remain literal. -/
def guard (i j : Nat) (leftKind rightKind : Bool) (e h k l : Int) (a : Nat) : Matrix :=
  .conjunction (domainMatrix i leftKind e h)
    (.conjunction (domainMatrix j rightKind k l)
      (.conjunction (atMost (valueTerm j rightKind k l) (valueTerm i leftKind e h))
        (atMost (valueTerm i leftKind e h) (.multiply a (.variable j)))))

def finiteCases (i j : Nat) (leftKind rightKind : Bool) (e h k l : Int)
    (a : Nat) (p : Matrix) : Matrix :=
  Matrix.any ((List.range (bound rightKind k l a)).map (fun n =>
    (Matrix.conjunction (guard i j leftKind rightKind e h k l a) p).substitute j (.numeral n)))

namespace Code
abbrev Input := (Nat × Nat) × ((Bool × Bool) × ((Int × Int) × ((Int × Int) × (Nat × Nat))))
def input (i j : Nat) (leftKind rightKind : Bool) (e h k l : Int) (a code : Nat) : Input :=
  ((i, j), ((leftKind, rightKind), ((e, h), ((k, l), (a, code)))))
def leftName (p : Input) : Nat := p.1.1
def rightName (p : Input) : Nat := p.1.2
def leftKind (p : Input) : Bool := p.2.1.1
def rightKind (p : Input) : Bool := p.2.1.2
def leftIndex (p : Input) : Int := p.2.2.1.1
def leftOuter (p : Input) : Int := p.2.2.1.2
def rightIndex (p : Input) : Int := p.2.2.2.1.1
def rightOuter (p : Input) : Int := p.2.2.2.1.2
def coefficient (p : Input) : Nat := p.2.2.2.2.1
def matrix (p : Input) : Nat := p.2.2.2.2.2

def value (i : Nat) (kind : Bool) (e h : Int) : Nat :=
  if kind then HyperWindowCode.value i e h
  else WindowCode.phi (WindowCode.shift (WindowCode.var i) e)
def domain (i : Nat) (kind : Bool) (e h : Int) : Nat :=
  if kind then HyperWindowCode.domain i e h else WindowCode.domain (WindowCode.var i) e
def bound (p : Input) : Nat := LinearWindow.bound (rightKind p) (rightIndex p) (rightOuter p) (coefficient p)
def guard (p : Input) : Nat :=
  WindowCode.conjunction (domain (leftName p) (leftKind p) (leftIndex p) (leftOuter p))
    (WindowCode.conjunction (domain (rightName p) (rightKind p) (rightIndex p) (rightOuter p))
      (WindowCode.conjunction
        (WindowCode.atMost (value (rightName p) (rightKind p) (rightIndex p) (rightOuter p))
          (value (leftName p) (leftKind p) (leftIndex p) (leftOuter p)))
        (WindowCode.atMost (value (leftName p) (leftKind p) (leftIndex p) (leftOuter p))
          (WindowCode.multiply (coefficient p) (WindowCode.var (rightName p))))))
def finiteCases (p : Input) : Nat :=
  WindowCode.any ((List.range (bound p)).map (fun n =>
    WindowCode.matrixSubstitute (rightName p) (WindowCode.numeral n)
      (WindowCode.conjunction (guard p) (matrix p))))
end Code

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearWindow
