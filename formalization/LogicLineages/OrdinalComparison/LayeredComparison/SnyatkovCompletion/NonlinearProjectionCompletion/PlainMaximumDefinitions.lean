module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.BlockRowsDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.DominantBoundaryDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainMaximum
open BlockRows

/-- The actual source graph compiler emits only Phi(variable) with shift zero.
All non-bound occurrences must first be moved to tied parameter constants. -/
def allowedSummand (bound : List Nat) : NormalForm.Summand → Bool
  | .variable j => bound.contains j
  | .phi j shift => bound.contains j && decide (shift = 0)
  | .hyperPhi _ _ _ => false
def allowed (bound : List Nat) (r : Row) : Bool :=
  r.2.all (fun a => allowedSummand bound a.2)

def isHead (i : Nat) : NormalForm.Summand → Bool
  | .phi j shift => (j == i) && decide (shift = 0)
  | _ => false
def headCoefficient (i : Nat) (r : Row) : Int :=
  (r.2.map (fun a => if isHead i a.2 then a.1 else 0)).sum
def remainingOccurrences (i : Nat) (r : Row) : List (Int × NormalForm.Summand) :=
  r.2.filter (fun a => !isHead i a.2)
def remainderValue (i : Nat) (r : Row) (ν : Nat → Nat) : Int :=
  ((remainingOccurrences i r).map (fun a => a.1 * (a.2.term.value ν : Int))).sum
def dropHead (i : Nat) (r : Row) : Row := (r.1, remainingOccurrences i r)
def constantValue (r : Row) (ν : Nat → Nat) : Int :=
  (r.1.1.value ν : Int) - (r.1.2.value ν : Int)
def mass (r : Row) : Nat := (r.2.map (fun a => a.1.natAbs)).sum
def cutoff (r : Row) : Nat := 4 * mass r + 1

def UniqueMaximum (bound : List Nat) (i : Nat) (ν : Nat → Nat) : Prop :=
  i ∈ bound ∧ ∀ j ∈ bound, j ≠ i → ν j < ν i

def absoluteConstant (r : Row) : Term :=
  .add (.subtract r.1.1 r.1.2) (.subtract r.1.2 r.1.1)
def boundary (i : Nat) (r : Row) : Term :=
  DominantBoundary.center (headCoefficient i r).natAbs (absoluteConstant r)

/-- The coefficient-zero case has no nonlinear selected head. Otherwise this
is the literal complement of the mathematical five-position inverse band. -/
def OutsideBoundary (i : Nat) (r : Row) (ν : Nat → Nat) : Prop :=
  headCoefficient i r = 0 ∨
    ν i < (boundary i r).value ν - 2 ∨ (boundary i r).value ν + 2 < ν i

def positiveGuard (i : Nat) (r : Row) : Formula :=
  .disjunction (.atom (.nonnegative (r.1, [])))
    (.atom (.nonnegative ((.numeral 0, .add (boundary i r) (.numeral 3)),
      [(1, .variable i)])))
def negativeGuard (i : Nat) (r : Row) : Formula :=
  .conjunction
    (.atom (.nonnegative ((r.1.1, .add r.1.2 (.numeral 1)), [])))
    (.atom (.nonnegative ((.subtract (boundary i r) (.numeral 2), .numeral 1),
      [(-1, .variable i)])))

/-- Every source row is handled separately. A row without the selected
surviving head keeps its own literal linear/other-name remainder; it is not
assigned a fictitious copy of another row's dominant summand. -/
def linearizeNonnegative (i : Nat) (r : Row) : Formula :=
  if 0 < headCoefficient i r then positiveGuard i r
  else if headCoefficient i r < 0 then negativeGuard i r
  else .atom (.nonnegative (dropHead i r))

def occurrences : Formula → List (Int × NormalForm.Summand)
  | .truth | .falsity => []
  | .atom a => a.row.2
  | .negative p => occurrences p
  | .conjunction p q | .disjunction p q => occurrences p ++ occurrences q
def linearSummand (i : Nat) : NormalForm.Summand → Bool
  | .variable _ => true
  | .phi j _ | .hyperPhi j _ _ => j != i
def linearIn (i : Nat) (p : Formula) : Bool :=
  (!p.parameters.contains i) && (occurrences p).all (fun a => linearSummand i a.2)

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainMaximum
