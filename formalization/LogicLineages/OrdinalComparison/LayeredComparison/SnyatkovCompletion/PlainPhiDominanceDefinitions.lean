module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NormalFormDefinitions
public import LogicLineages.OrdinalComparison.CommonHeadCollectedRowDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainPhiDominance
open NormalForm

/-- Exact original row test, without cancelling zero coefficients first. -/
def isPlain (r : Row) : Bool := r.2.all (fun a => match a.2 with
  | .variable _ | .phi _ _ => true
  | .hyperPhi _ _ _ => false)

def mass (r : Row) : Nat := (r.2.map (fun a => a.1.natAbs)).sum

def shiftMass (r : Row) : Nat := (r.2.map (fun a => match a.2 with
  | .phi _ e => e.natAbs
  | _ => 0)).sum

def threshold (r : Row) : Nat :=
  shiftMass r + 2 * mass r + mass r * shiftMass r + r.1.natAbs + 1

def argument (ν : Nat → Nat) (i : Nat) (e : Int) : Nat := ((ν i : Int) + e).toNat

/-- All original nonlinear occurrences, evaluated at one shared valuation.
Equal arguments are collected only after this literal map. -/
def phiData (r : Row) (ν : Nat → Nat) : CommonHeadLargeRow.Row :=
  r.2.flatMap (fun a => match a.2 with
    | .phi i e => [(a.1, argument ν i e)]
    | _ => [])

def linearPart (r : Row) (ν : Nat → Nat) : Int :=
  r.1 + (r.2.map (fun a => match a.2 with
    | .variable i => a.1 * (ν i : Int)
    | _ => 0)).sum

/-- Current provenance: the name has an original Phi occurrence whose entire
actual equal-argument coefficient block survives. Deleted blocks confer no
maximal-variable provenance. -/
def active (i : Nat) (r : Row) (ν : Nat → Nat) : Bool :=
  r.2.any (fun a => match a.2 with
    | .phi j e => j == i &&
        CommonHeadCollectedRow.coefficient (phiData r ν) (argument ν j e) != 0
    | _ => false)

namespace Code
def isPlain (r : NormalForm.Code.RowData) : Bool := r.2.all (fun a => decide (a.2.1 ≤ 1))
def mass (r : NormalForm.Code.RowData) : Nat := (r.2.map (fun a => a.1.natAbs)).sum
def shiftMass (r : NormalForm.Code.RowData) : Nat :=
  (r.2.map (fun a => if a.2.1 = 1 then a.2.2.2.1.natAbs else 0)).sum
def threshold (r : NormalForm.Code.RowData) : Nat :=
  shiftMass r + 2 * mass r + mass r * shiftMass r + r.1.natAbs + 1
end Code

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainPhiDominance
