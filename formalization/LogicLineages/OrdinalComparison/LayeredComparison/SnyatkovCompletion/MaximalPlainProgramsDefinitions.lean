module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainRowsDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.InactivePhiProgramsDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainPrograms.Code

def ownIndices (i : Nat) (r : NormalForm.Code.RowData) : List Nat :=
  (List.range (ShiftedInputPrograms.Code.occurrences r).length).filter
    (fun k => ((ShiftedInputPrograms.Code.inputs r).getD k (0, 0)).1 == i)
def activeGuard (i : Nat) (r : NormalForm.Code.RowData) : Nat :=
  InactivePhiPrograms.Code.any ((ownIndices i r).map (fun k =>
    ShiftedInputPrograms.Code.negative (ShiftedInputPrograms.Code.block r k 0)))

def residueSplit (i m : Nat) (xs : List (Int × NormalForm.Code.ItemData)) :
    Int × List (Int × NormalForm.Code.ItemData) :=
  xs.foldr (fun a rest => if a.2.1 = 1 ∧ a.2.2.1 = i then
    (a.1 * (fastControlResidue m : Int) + rest.1, rest.2)
    else (rest.1, a :: rest.2)) (0, [])
def residueRow (i m : Nat) (r : NormalForm.Code.RowData) : NormalForm.Code.RowData :=
  let parts := residueSplit i m r.2
  (r.1 + parts.1, parts.2)

def nonnegative (i : Nat) (r : NormalForm.Code.RowData) : Nat :=
  ShiftedInputPrograms.Code.disjunction (InactivePhiPrograms.Code.compileAtom i (0, 0, r))
    (ShiftedInputPrograms.Code.conjunction (activeGuard i r)
      (ShiftedInputPrograms.Code.disjunction
        (ShiftedInputPrograms.Code.activeSign r 0) (ShiftedInputPrograms.Code.activeSign r 1)))
def cutoff (a : NormalForm.Code.AtomData) : Nat :=
  if a.1 = 0 then PlainPhiDominance.Code.threshold a.2.2
  else PlainPhiDominance.Code.shiftMass a.2.2 + (a.2.1 + 1)
def compileAtom (i : Nat) (a : NormalForm.Code.AtomData) : Nat :=
  if a.1 = 0 then nonnegative i a.2.2
  else InactivePhiPrograms.Code.atom (1, a.2.1, residueRow i (a.2.1 + 1) a.2.2)

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainPrograms.Code
