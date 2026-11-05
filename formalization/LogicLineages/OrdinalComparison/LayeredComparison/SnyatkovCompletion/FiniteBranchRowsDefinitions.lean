module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedRowsDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ActiveHyperDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteBranchRows
open NormalForm

def nonlinear (i : Nat) (kind : Bool) (e h : Int) : Summand :=
  if kind then .hyperPhi i e h else .phi i e
def leRow (s t : Summand) (c : Nat) : Row := (0, [(-1, s), ((c : Int), t)])
def guardedLe (s t : Summand) (c : Nat) : Formula := guardedAtom (.nonnegative (leRow s t c))
def linearGuard (i j : Nat) (leftKind rightKind : Bool) (e h k l : Int) (a : Nat) : Formula :=
  .conjunction (guardedLe (nonlinear j rightKind k l) (nonlinear i leftKind e h) 1)
    (guardedLe (nonlinear i leftKind e h) (.variable j) a)
def activeGuard (i j : Nat) (kind : Bool) (e h k l q : Int) (a : Nat) : Formula :=
  .conjunction (guardedLe (.hyperPhi j k l) (nonlinear i kind e h) 1)
    (guardedLe (nonlinear i kind e h) (.phi j q) a)
def linearCases (i j : Nat) (leftKind rightKind : Bool) (e h k l : Int) (a : Nat)
    (p : Formula) : Formula :=
  BoundedRows.bounded j (LinearWindow.bound rightKind k l a)
    (.conjunction (linearGuard i j leftKind rightKind e h k l a) p)
def activeCases (i j : Nat) (kind : Bool) (e h k l q : Int) (a : Nat) (p : Formula) : Formula :=
  BoundedRows.bounded j (ActiveHyper.bound k l q a)
    (.conjunction (activeGuard i j kind e h k l q a) p)

namespace Code
def nonlinear (i : Nat) (kind : Bool) (e h : Int) : NormalForm.Code.ItemData :=
  if kind then (2, i, e, h) else (1, i, e, 0)
def var (i : Nat) : NormalForm.Code.ItemData := (0, i, 0, 0)
def phi (i : Nat) (e : Int) : NormalForm.Code.ItemData := (1, i, e, 0)
def hyper (i : Nat) (e h : Int) : NormalForm.Code.ItemData := (2, i, e, h)
def conjunction (a b : Nat) : Nat := 6 * Nat.pair a b + 4
def nonnegative (row : NormalForm.Code.RowData) : Nat :=
  6 * Encodable.encode ((0, 0, row) : NormalForm.Code.AtomData) + 2
def leRow (s t : NormalForm.Code.ItemData) (c : Nat) : NormalForm.Code.RowData :=
  (0, [(-1, s), ((c : Int), t)])
def domains (row : NormalForm.Code.RowData) : Nat :=
  row.2.foldr (fun a rest => conjunction (nonnegative (NormalForm.Code.domainRowData a.2)) rest) 0
def guardedLe (s t : NormalForm.Code.ItemData) (c : Nat) : Nat :=
  conjunction (domains (leRow s t c)) (nonnegative (leRow s t c))
def linearGuard (p : LinearWindow.Code.Input) : Nat :=
  let lead := nonlinear (LinearWindow.Code.leftName p) (LinearWindow.Code.leftKind p)
    (LinearWindow.Code.leftIndex p) (LinearWindow.Code.leftOuter p)
  let active := nonlinear (LinearWindow.Code.rightName p) (LinearWindow.Code.rightKind p)
    (LinearWindow.Code.rightIndex p) (LinearWindow.Code.rightOuter p)
  conjunction (guardedLe active lead 1)
    (guardedLe lead (var (LinearWindow.Code.rightName p)) (LinearWindow.Code.coefficient p))
def activeGuard (p : ActiveHyper.Code.Input) : Nat :=
  let lead := nonlinear (ActiveHyper.Code.leftName p) (ActiveHyper.Code.kind p)
    (ActiveHyper.Code.leftIndex p) (ActiveHyper.Code.leftOuter p)
  conjunction (guardedLe
      (hyper (ActiveHyper.Code.rightName p) (ActiveHyper.Code.activeIndex p) (ActiveHyper.Code.activeOuter p)) lead 1)
    (guardedLe lead (phi (ActiveHyper.Code.rightName p) (ActiveHyper.Code.plainShift p))
      (ActiveHyper.Code.coefficient p))
def linearCases (p : LinearWindow.Code.Input) : Nat :=
  BoundedRows.Code.bounded (LinearWindow.Code.rightName p) (LinearWindow.Code.bound p)
    (conjunction (linearGuard p) (LinearWindow.Code.matrix p))
def activeCases (p : ActiveHyper.Code.Input) : Nat :=
  BoundedRows.Code.bounded (ActiveHyper.Code.rightName p) (ActiveHyper.Code.bound p)
    (conjunction (activeGuard p) (ActiveHyper.Code.matrix p))
end Code

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteBranchRows
