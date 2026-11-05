module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SignedRowsDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteBranchRowsDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.HyperBranchRows
open NormalForm

def closeGuard (i j : Nat) (e h k l : Int) (c : Nat) : Formula :=
  .conjunction
    (FiniteBranchRows.guardedLe (.hyperPhi j k l) (.hyperPhi i e h) 1)
    (FiniteBranchRows.guardedLe (.hyperPhi i e h) (.hyperPhi j k l) c)

/-- Equality of signed integer indices, used together with the original
nonnegative-index domains in closeGuard. -/
def indexEquality (i j : Nat) (e k : Int) : Formula :=
  .conjunction
    (.atom (.nonnegative (e - k, [(1, .variable i), (-1, .variable j)])))
    (.atom (.nonnegative (k - e, [(-1, .variable i), (1, .variable j)])))

def leftCases (i j : Nat) (e h k l : Int) (c : Nat) (p : Formula) : Formula :=
  BoundedRows.bounded i (HyperWindow.leftBound e h l)
    (.conjunction (closeGuard i j e h k l c) p)
def rightCases (i j : Nat) (e h k l : Int) (c : Nat) (p : Formula) : Formula :=
  BoundedRows.bounded j (HyperWindow.rightBound h k l c)
    (.conjunction (closeGuard i j e h k l c) p)
def equalCases (i j : Nat) (e h k l : Int) (c : Nat) (p : Formula) : Formula :=
  SignedRows.substitute i j (k - e)
    (.conjunction (indexEquality i j e k) (.conjunction (closeGuard i j e h k l c) p))

namespace Code
abbrev Input := HyperWindowCode.Input
def closeGuard (p : Input) : Nat :=
  let s := FiniteBranchRows.Code.hyper (HyperWindowCode.leftName p)
    (HyperWindowCode.leftIndex p) (HyperWindowCode.leftOuter p)
  let t := FiniteBranchRows.Code.hyper (HyperWindowCode.rightName p)
    (HyperWindowCode.rightIndex p) (HyperWindowCode.rightOuter p)
  FiniteBranchRows.Code.conjunction (FiniteBranchRows.Code.guardedLe t s 1)
    (FiniteBranchRows.Code.guardedLe s t (HyperWindowCode.coefficient p))
def indexEquality (p : Input) : Nat :=
  let x := FiniteBranchRows.Code.var (HyperWindowCode.leftName p)
  let y := FiniteBranchRows.Code.var (HyperWindowCode.rightName p)
  FiniteBranchRows.Code.conjunction
    (FiniteBranchRows.Code.nonnegative
      (HyperWindowCode.leftIndex p - HyperWindowCode.rightIndex p, [(1, x), (-1, y)]))
    (FiniteBranchRows.Code.nonnegative
      (HyperWindowCode.rightIndex p - HyperWindowCode.leftIndex p, [(-1, x), (1, y)]))
def leftCases (p : Input) : Nat :=
  BoundedRows.Code.bounded (HyperWindowCode.leftName p) (HyperWindowCode.leftBound p)
    (FiniteBranchRows.Code.conjunction (closeGuard p) (HyperWindowCode.matrix p))
def rightCases (p : Input) : Nat :=
  BoundedRows.Code.bounded (HyperWindowCode.rightName p) (HyperWindowCode.rightBound p)
    (FiniteBranchRows.Code.conjunction (closeGuard p) (HyperWindowCode.matrix p))
def equalCases (p : Input) : Nat :=
  SignedRows.Code.substitute (HyperWindowCode.leftName p) (HyperWindowCode.rightName p)
    (HyperWindowCode.rightIndex p - HyperWindowCode.leftIndex p)
    (FiniteBranchRows.Code.conjunction (indexEquality p)
      (FiniteBranchRows.Code.conjunction (closeGuard p) (HyperWindowCode.matrix p)))
end Code

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.HyperBranchRows
