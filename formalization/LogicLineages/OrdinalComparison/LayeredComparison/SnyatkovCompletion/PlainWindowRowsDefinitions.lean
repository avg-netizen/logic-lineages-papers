module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NestedRowsDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteBranchRowsDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ReverseWindowDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainWindowRows
open NormalForm

/-- Both original shifted Phi domains are retained, including coefficient zero. -/
def plusGuard (i j : Nat) (e k : Int) (c : Nat) : Formula :=
  .conjunction
    (FiniteBranchRows.guardedLe (.phi j k) (.phi i e) 1)
    (FiniteBranchRows.guardedLe (.phi i e) (.phi j k) c)
def minusGuard (i j : Nat) (e k : Int) (c : Nat) : Formula :=
  .conjunction
    (FiniteBranchRows.guardedLe (.phi i e) (.phi j k) 1)
    (FiniteBranchRows.guardedLe (.phi j k) (.phi i e) c)

def plusSubstitute (i j : Nat) (e k : Int) (d : Nat) (p : Formula) : Formula :=
  NestedRows.substitute i j k ((d : Int) - e) p
def minusSubstitute (i j : Nat) (e k : Int) (d : Nat) (p : Formula) : Formula :=
  NestedRows.substitute i j (k - (d : Int)) (-e) p
def plusCases (i j : Nat) (e k : Int) (c : Nat) (p : Formula) : Formula :=
  BoundedRows.any ((List.range (c + 1)).map (fun d =>
    plusSubstitute i j e k d (.conjunction (plusGuard i j e k c) p)))
def minusCases (i j : Nat) (e k : Int) (c : Nat) (p : Formula) : Formula :=
  BoundedRows.any ((List.range (c + 1)).map (fun d =>
    minusSubstitute i j e k d (.conjunction (minusGuard i j e k c) p)))

namespace Code
/-- Two original names, both signed shifts, coefficient, and a radix-six body. -/
abbrev Input := (Nat × Nat) × ((Int × Int) × (Nat × Nat))
def input (i j : Nat) (e k : Int) (c code : Nat) : Input := ((i, j), ((e, k), (c, code)))
def leftName (p : Input) : Nat := p.1.1
def rightName (p : Input) : Nat := p.1.2
def leftShift (p : Input) : Int := p.2.1.1
def rightShift (p : Input) : Int := p.2.1.2
def coefficient (p : Input) : Nat := p.2.2.1
def body (p : Input) : Nat := p.2.2.2
def plusGuard (p : Input) : Nat :=
  let s := FiniteBranchRows.Code.phi (leftName p) (leftShift p)
  let t := FiniteBranchRows.Code.phi (rightName p) (rightShift p)
  FiniteBranchRows.Code.conjunction (FiniteBranchRows.Code.guardedLe t s 1)
    (FiniteBranchRows.Code.guardedLe s t (coefficient p))
def minusGuard (p : Input) : Nat :=
  let s := FiniteBranchRows.Code.phi (leftName p) (leftShift p)
  let t := FiniteBranchRows.Code.phi (rightName p) (rightShift p)
  FiniteBranchRows.Code.conjunction (FiniteBranchRows.Code.guardedLe s t 1)
    (FiniteBranchRows.Code.guardedLe t s (coefficient p))
def plusSubstitute (p : Input) (d : Nat) : Nat :=
  NestedRows.Code.substitute (leftName p) (rightName p) (rightShift p)
    ((d : Int) - leftShift p) (body p)
def minusSubstitute (p : Input) (d : Nat) : Nat :=
  NestedRows.Code.substitute (leftName p) (rightName p) (rightShift p - (d : Int))
    (-leftShift p) (body p)
def plusCases (p : Input) : Nat :=
  BoundedRows.Code.any ((List.range (coefficient p + 1)).map (fun d =>
    plusSubstitute (input (leftName p) (rightName p) (leftShift p) (rightShift p)
      (coefficient p) (FiniteBranchRows.Code.conjunction (plusGuard p) (body p))) d))
def minusCases (p : Input) : Nat :=
  BoundedRows.Code.any ((List.range (coefficient p + 1)).map (fun d =>
    minusSubstitute (input (leftName p) (rightName p) (leftShift p) (rightShift p)
      (coefficient p) (FiniteBranchRows.Code.conjunction (minusGuard p) (body p))) d))
end Code

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainWindowRows
