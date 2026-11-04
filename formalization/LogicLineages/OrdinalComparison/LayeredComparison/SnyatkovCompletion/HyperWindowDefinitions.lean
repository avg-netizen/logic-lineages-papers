module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.WindowDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovHyperCollisionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.HyperWindow

def indexTerm (i : Nat) (e : Int) : Term := shiftTerm (.variable i) e
def innerTerm (i : Nat) (e h : Int) : Term := shiftTerm (.hyper (indexTerm i e)) h
def valueTerm (i : Nat) (e h : Int) : Term := .phi (innerTerm i e h)

/-- BOTH original signed domains are retained: the hyper-index and the outer
Phi argument. The total arithmetic syntax never supplies a new source domain. -/
def domainMatrix (i : Nat) (e h : Int) : Matrix :=
  .conjunction (shiftDomain (.variable i) e) (shiftDomain (.hyper (indexTerm i e)) h)

def closeMatrix (i j : Nat) (e h k l : Int) (c : Nat) : Matrix :=
  .conjunction (domainMatrix i e h) (.conjunction (domainMatrix j k l)
    (.conjunction (atMost (valueTerm j k l) (valueTerm i e h))
      (atMost (valueTerm i e h) (.multiply c (valueTerm j k l)))))

/-- Actual bounds apply to the SMALLER shifted hyper-index. Signed index
translation then gives the displayed raw-variable finite enumeration bounds. -/
def leftBound (e h l : Int) : Nat :=
  SnyatkovHyperCollision.collisionBound 1 l h + e.natAbs + 1
def rightBound (h k l : Int) (c : Nat) : Nat :=
  SnyatkovHyperCollision.collisionBound c h l + k.natAbs + 1

def leftCases (i j : Nat) (e h k l : Int) (c : Nat) (p : Matrix) : Matrix :=
  Matrix.any ((List.range (leftBound e h l)).map (fun n =>
    (Matrix.conjunction (closeMatrix i j e h k l c) p).substitute i (.numeral n)))

def rightCases (i j : Nat) (e h k l : Int) (c : Nat) (p : Matrix) : Matrix :=
  Matrix.any ((List.range (rightBound h k l c)).map (fun n =>
    (Matrix.conjunction (closeMatrix i j e h k l c) p).substitute j (.numeral n)))

/-- Equality of the actual shifted indices allows one exact signed affine
substitution; the original equality and all source domains stay in the branch. -/
def equalCases (i j : Nat) (e h k l : Int) (c : Nat) (p : Matrix) : Matrix :=
  (Matrix.conjunction (.equal (indexTerm i e) (indexTerm j k))
    (.conjunction (closeMatrix i j e h k l c) p)).substitute i
      (shiftTerm (.variable j) (k - e))

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.HyperWindow
