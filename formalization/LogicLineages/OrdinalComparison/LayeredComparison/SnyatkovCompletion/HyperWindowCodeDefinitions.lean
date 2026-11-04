module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.HyperWindowDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.WindowCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.HyperWindowCode

/-- Grouped original data: two names, their two signed inner/outer shifts,
the original comparison coefficient and the actual matrix code. -/
abbrev Input := (Nat × Nat) × ((Int × Int) × ((Int × Int) × (Nat × Nat)))
def input (i j : Nat) (e h k l : Int) (c code : Nat) : Input :=
  ((i, j), ((e, h), ((k, l), (c, code))))
def leftName (p : Input) : Nat := p.1.1
def rightName (p : Input) : Nat := p.1.2
def leftIndex (p : Input) : Int := p.2.1.1
def leftOuter (p : Input) : Int := p.2.1.2
def rightIndex (p : Input) : Int := p.2.2.1.1
def rightOuter (p : Input) : Int := p.2.2.1.2
def coefficient (p : Input) : Nat := p.2.2.2.1
def matrix (p : Input) : Nat := p.2.2.2.2

def hyper (a : Nat) : Nat := 10 * a + 7
def equal (a b : Nat) : Nat := 8 * Nat.pair a b + 2
def index (i : Nat) (e : Int) : Nat := WindowCode.shift (WindowCode.var i) e
def value (i : Nat) (e h : Int) : Nat :=
  WindowCode.phi (WindowCode.shift (hyper (index i e)) h)
def domain (i : Nat) (e h : Int) : Nat :=
  WindowCode.conjunction (WindowCode.domain (WindowCode.var i) e)
    (WindowCode.domain (hyper (index i e)) h)

def close (p : Input) : Nat :=
  WindowCode.conjunction (domain (leftName p) (leftIndex p) (leftOuter p))
    (WindowCode.conjunction (domain (rightName p) (rightIndex p) (rightOuter p))
      (WindowCode.conjunction
        (WindowCode.atMost (value (rightName p) (rightIndex p) (rightOuter p))
          (value (leftName p) (leftIndex p) (leftOuter p)))
        (WindowCode.atMost (value (leftName p) (leftIndex p) (leftOuter p))
          (WindowCode.multiply (coefficient p)
            (value (rightName p) (rightIndex p) (rightOuter p))))))

def guarded (p : Input) : Nat := WindowCode.conjunction (close p) (matrix p)
def leftBound (p : Input) : Nat :=
  HyperWindow.leftBound (leftIndex p) (leftOuter p) (rightOuter p)
def rightBound (p : Input) : Nat :=
  HyperWindow.rightBound (leftOuter p) (rightIndex p) (rightOuter p) (coefficient p)

def leftCases (p : Input) : Nat :=
  WindowCode.any ((List.range (leftBound p)).map (fun n =>
    WindowCode.matrixSubstitute (leftName p) (WindowCode.numeral n) (guarded p)))

def rightCases (p : Input) : Nat :=
  WindowCode.any ((List.range (rightBound p)).map (fun n =>
    WindowCode.matrixSubstitute (rightName p) (WindowCode.numeral n) (guarded p)))

def equalCases (p : Input) : Nat :=
  WindowCode.matrixSubstitute (leftName p)
    (WindowCode.shift (WindowCode.var (rightName p)) (rightIndex p - leftIndex p))
    (WindowCode.conjunction
      (equal (index (leftName p) (leftIndex p)) (index (rightName p) (rightIndex p)))
      (guarded p))

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.HyperWindowCode
