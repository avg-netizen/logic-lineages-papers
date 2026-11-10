module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockLinearizationCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockDispatchCode

abbrev RowData := BlockRowSubstitutionCode.RowData
abbrev AtomData := BlockFormulaSubstitutionCode.AtomData
abbrev StateData := List Nat × Nat

def stateData (s : PlainBlockSplit.State) : StateData :=
  (s.1, BlockFormulaSubstitutionCode.formulaCode s.2)

/-- Rename only the occurrence name. Literal raw tags, both shifts, weights
and signed parameter term codes retain their original positions and values. -/
def renameItem (i j : Nat) (s : NormalForm.Code.ItemData) : NormalForm.Code.ItemData :=
  (s.1, (if s.2.1 = i then j else s.2.1), s.2.2.1, s.2.2.2)
def renameRow (i j : Nat) (r : RowData) : RowData :=
  (r.1, r.2.map (fun a => (a.1, renameItem i j a.2)))
def renameEncodedAtom (i j payload : Nat) : Nat :=
  let a := BlockFormulaSubstitutionCode.decodeAtom payload
  Encodable.encode ((a.1, a.2.1, renameRow i j a.2.2) : AtomData)
def rename (i j code : Nat) : Nat :=
  LinearRows.Code.mapAtoms (renameEncodedAtom i j) code

/-- The first bound name is selected literally, and erase removes its first
occurrence. No deduplication or nonempty-bound precondition is introduced. -/
def small (bound : List Nat) (code : Nat) : List StateData :=
  match bound with
  | [] => []
  | i :: _ => (List.range (PlainBlockLinearizationCode.cutoff code)).map (fun n =>
      (bound.erase i, BlockFormulaSubstitutionCode.formula i (WindowCode.numeral n) code))
def ties (bound : List Nat) (code : Nat) : List StateData :=
  bound.flatMap (fun i => (bound.filter (fun j => j != i)).map (fun j =>
    (bound.erase i, rename i j code)))
def bands (bound : List Nat) (code : Nat) : List StateData :=
  bound.flatMap (fun i => (LinearRows.Code.atoms code).flatMap (fun payload =>
    let a := BlockFormulaSubstitutionCode.decodeAtom payload
    if a.1 = 0 then
      if PlainBlockLinearizationCode.headCoefficient i a.2.2 = 0 then [] else
        (List.range 5).map (fun d => (bound.erase i,
          BlockFormulaSubstitutionCode.formula i
            (PlainBlockLinearizationCode.bandCandidate i a.2.2 d) code))
    else []))

/-- Assemble the SAME maximum frame, outside-band guard and linearized body,
then invoke the actual accepted tied-table Cooper/lower program. -/
def far (bound : List Nat) (code : Nat) : List StateData :=
  bound.map (fun i => (bound.erase i, TiedLinearCode.eliminate i
    (PlainBlockLinearizationCode.conjunction (PlainBlockLinearizationCode.frame bound i code)
      (PlainBlockLinearizationCode.conjunction (PlainBlockLinearizationCode.outside i code)
        (PlainBlockLinearizationCode.linearize i code)))))
def branches (bound : List Nat) (code : Nat) : List StateData :=
  small bound code ++ ties bound code ++ bands bound code ++ far bound code

/-- Finished states survive exactly once. Every unfinished state takes the
original finite branch dispatcher; order and duplicate states are retained. -/
def advance (states : List StateData) : List StateData :=
  states.flatMap (fun s => if s.1 = [] then [s] else branches s.1 s.2)
def run (fuel : Nat) (states : List StateData) : List StateData :=
  advance^[fuel] states

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockDispatchCode
