module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.QuantifiedLinearDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ClosedLinear
open NormalForm SourceRows

/-- Literal absence of every row occurrence; cancelled and zero-weight
occurrences still prevent acceptance as a constant matrix. -/
def constantMatrix (p : Formula) : Bool :=
  (LinearRows.atoms p).all (fun a => a.row.2.isEmpty)

def constantAtom : Atom → Bool
  | .nonnegative row => decide (0 ≤ row.1)
  | .divisible m row => decide (row.1.natAbs % (m + 1) = 0)

/-- Computes only constant row components. Its semantic contract requires the
literal constant-matrix test, so no nonlinear evaluator is assumed. -/
def evaluateConstants : Formula → Bool
  | .truth => true
  | .falsity => false
  | .atom a => constantAtom a
  | .negative p => !evaluateConstants p
  | .conjunction p q => evaluateConstants p && evaluateConstants q
  | .disjunction p q => evaluateConstants p || evaluateConstants q

/-- An explicit rejecting decider: `none` means outside the closed admissible
fragment, not that the sentence is false. -/
def decideClosed (p : QFormula) : Option Bool :=
  if QuantifiedLinear.admissible p && constantMatrix (QuantifiedLinear.eliminate p)
  then some (evaluateConstants (QuantifiedLinear.eliminate p)) else none

namespace Code
def constantMatrix (code : Nat) : Bool :=
  (LinearRows.Code.atoms code).all (fun a => (LinearRows.Code.decodeAtom a).2.2.2.isEmpty)

def constantAtom (a : NormalForm.Code.AtomData) : Bool :=
  if a.1 = 0 then decide (0 ≤ a.2.2.1)
  else decide (a.2.2.1.natAbs % (a.2.1 + 1) = 0)

def evaluateConstants (code : Nat) : Bool :=
  if code % 6 = 0 then true
  else if code % 6 = 1 then false
  else if code % 6 = 2 then constantAtom (LinearRows.Code.decodeAtom (code / 6))
  else if code % 6 = 3 then !evaluateConstants (code / 6)
  else if code % 6 = 4 then
    evaluateConstants (code / 6).unpair.1 && evaluateConstants (code / 6).unpair.2
  else evaluateConstants (code / 6).unpair.1 || evaluateConstants (code / 6).unpair.2
termination_by code
decreasing_by
  all_goals
    have hpos : 0 < code := by omega
    have hd : code / 6 < code := Nat.div_lt_self hpos (by decide)
    have hl := Nat.unpair_left_le (code / 6)
    have hr := Nat.unpair_right_le (code / 6)
    omega

def decideClosed (code : Nat) : Option Bool :=
  if QuantifiedLinear.Code.admissible code && constantMatrix (QuantifiedLinear.Code.eliminate code)
  then some (evaluateConstants (QuantifiedLinear.Code.eliminate code)) else none
end Code

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ClosedLinear
