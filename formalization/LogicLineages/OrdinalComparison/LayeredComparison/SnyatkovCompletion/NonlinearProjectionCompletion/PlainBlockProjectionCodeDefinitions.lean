module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockDispatchCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockProjectionCode

abbrev RowData := BlockRowSubstitutionCode.RowData
abbrev AtomData := BlockFormulaSubstitutionCode.AtomData
abbrev StateData := PlainBlockDispatchCode.StateData

/-- Preserve both signed parameter terms and the original right-fold of all
weighted occurrences, including zero coefficients and duplicate occurrences. -/
def positiveTerm (r : RowData) : Nat :=
  WindowCode.add r.1.1 (r.2.foldr (fun a rest =>
    WindowCode.add (WindowCode.multiply a.1.toNat (NormalForm.Code.itemTerm a.2)) rest)
      (WindowCode.numeral 0))
def negativeTerm (r : RowData) : Nat :=
  WindowCode.add r.1.2 (r.2.foldr (fun a rest =>
    WindowCode.add (WindowCode.multiply (-a.1).toNat (NormalForm.Code.itemTerm a.2)) rest)
      (WindowCode.numeral 0))
def absoluteTerm (r : RowData) : Nat :=
  WindowCode.add (WindowCode.subtract (positiveTerm r) (negativeTerm r))
    (WindowCode.subtract (negativeTerm r) (positiveTerm r))

/-- Literal radix-eight output of the original block-atom compiler. Raw tag
zero selects nonnegative; every other tag selects the original positive modulus
branch. Malformed payloads use the already fixed block-atom decoder. -/
def atom (a : AtomData) : Nat :=
  if a.1 = 0 then WindowCode.atMost (negativeTerm a.2.2) (positiveTerm a.2.2)
  else 8 * Nat.pair (a.2.1 + 1) (absoluteTerm a.2.2) + 4

def formula (code : Nat) : Nat :=
  if code % 6 = 0 then 0
  else if code % 6 = 1 then 1
  else if code % 6 = 2 then atom (BlockFormulaSubstitutionCode.decodeAtom (code / 6))
  else if code % 6 = 3 then WindowCode.negative (formula (code / 6))
  else 8 * Nat.pair (formula (code / 6).unpair.1)
    (formula (code / 6).unpair.2) + (code % 6 + 2)
termination_by code
decreasing_by
  all_goals
    have hpos : 0 < code := by omega
    have hd : code / 6 < code := Nat.div_lt_self hpos (by decide)
    have hl := Nat.unpair_left_le (code / 6)
    have hr := Nat.unpair_right_le (code / 6)
    omega

/-- Ignore the residual bound-list component exactly as the original output
readout does. Do not filter unfinished states, deduplicate or reassociate output. -/
def readout (states : List StateData) : Nat :=
  WindowCode.any (states.map (fun s => formula s.2))

/-- The same accepted dispatcher, same bound-length fuel and same singleton
initial state, followed by the literal compiled-matrix disjunction readout. -/
def project (bound : List Nat) (code : Nat) : Nat :=
  readout (PlainBlockDispatchCode.run bound.length [(bound, code)])

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockProjectionCode
