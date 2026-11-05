module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.InactivePhiRowsDefinitions
public import LogicLineages.OrdinalComparison.ControlResidueDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainRows
open NormalForm

/-- Only original Phi occurrence indices belonging to the chosen raw name. -/
def ownIndices (i : Nat) (r : Row) : List Nat :=
  (List.range (ShiftedInputGuards.occurrences r).length).filter
    (fun k => ((ShiftedInputGuards.inputs r).getD k (0, 0)).1 == i)
def activeGuard (i : Nat) (r : Row) : Formula :=
  BoundedRows.any ((ownIndices i r).map (fun k =>
    .negative (ShiftedInputGuards.block r k 0)))

/-- Keep all variable occurrences. Only Phi occurrences at the chosen name are
folded, using the actual common residue for this modulus. -/
def residueSplit (i m : Nat) (xs : List (Int × Summand)) : Int × List (Int × Summand) :=
  xs.foldr (fun a rest => match a.2 with
    | .phi j _ => if j = i then
        (a.1 * (fastControlResidue m : Int) + rest.1, rest.2)
      else (rest.1, a :: rest.2)
    | _ => (rest.1, a :: rest.2)) (0, [])
def residueRow (i m : Nat) (r : Row) : Row :=
  let parts := residueSplit i m r.2
  (r.1 + parts.1, parts.2)

def nonnegative (i : Nat) (r : Row) : Formula :=
  .disjunction (InactivePhiRows.compileAtom i (.nonnegative r))
    (.conjunction (activeGuard i r)
      (.disjunction (ShiftedInputGuards.activeSign r 0) (ShiftedInputGuards.activeSign r 1)))

def cutoff : Atom → Nat
  | .nonnegative r => PlainPhiDominance.threshold r
  | .divisible m r => PlainPhiDominance.shiftMass r + (m + 1)
def compileAtom (i : Nat) : Atom → Formula
  | .nonnegative r => nonnegative i r
  | .divisible m r => .atom (.divisible m (residueRow i (m + 1) r))

def retained (i : Nat) : Summand → Bool
  | .phi j _ => j != i
  | _ => true

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainRows
