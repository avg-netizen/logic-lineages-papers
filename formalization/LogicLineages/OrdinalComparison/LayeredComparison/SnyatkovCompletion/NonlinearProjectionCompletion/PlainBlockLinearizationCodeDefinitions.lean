module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockSplitDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.BlockFormulaSubstitutionCodeDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.TiedLinearCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockLinearizationCode

abbrev RowData := BlockRowSubstitutionCode.RowData
abbrev EntryData := BlockRowSubstitutionCode.EntryData
abbrev AtomData := BlockFormulaSubstitutionCode.AtomData

/-- The original block-formula encoding, not the expanded matrix encoding. -/
def nonnegative (r : RowData) : Nat := 6 * Encodable.encode ((0, 0, r) : AtomData) + 2
def divisible (m : Nat) (r : RowData) : Nat := 6 * Encodable.encode ((1, m, r) : AtomData) + 2
def conjunction (p q : Nat) : Nat := 6 * Nat.pair p q + 4
def disjunction (p q : Nat) : Nat := 6 * Nat.pair p q + 5
def all (codes : List Nat) : Nat := codes.foldr conjunction 0

/-- Only the literal selected shift-zero Phi head is removed. Raw data for
other tags and shifts are retained without validating or canonicalizing them. -/
def isHead (i : Nat) (s : NormalForm.Code.ItemData) : Bool :=
  (s.1 == 1) && (s.2.1 == i) && decide (s.2.2.1 = 0)
def headCoefficient (i : Nat) (r : RowData) : Int :=
  (r.2.map (fun a => if isHead i a.2 then a.1 else 0)).sum
def remainingOccurrences (i : Nat) (r : RowData) : List EntryData :=
  r.2.filter (fun a => !isHead i a.2)
def mass (r : RowData) : Nat := (r.2.map (fun a => a.1.natAbs)).sum
def absoluteConstant (r : RowData) : Nat :=
  WindowCode.add (WindowCode.subtract r.1.1 r.1.2) (WindowCode.subtract r.1.2 r.1.1)
def boundary (i : Nat) (r : RowData) : Nat :=
  DominantBoundary.Code.center (headCoefficient i r).natAbs (absoluteConstant r)

def positiveGuard (i : Nat) (r : RowData) : Nat :=
  disjunction (nonnegative (r.1, []))
    (nonnegative ((WindowCode.numeral 0, WindowCode.add (boundary i r) (WindowCode.numeral 3)),
      [(1, TiedLinearCode.variableItem i)]))
def negativeGuard (i : Nat) (r : RowData) : Nat :=
  conjunction
    (nonnegative ((r.1.1, WindowCode.add r.1.2 (WindowCode.numeral 1)), []))
    (nonnegative ((WindowCode.subtract (boundary i r) (WindowCode.numeral 2), WindowCode.numeral 1),
      [(-1, TiedLinearCode.variableItem i)]))
def linearizeNonnegative (i : Nat) (r : RowData) : Nat :=
  if 0 < headCoefficient i r then positiveGuard i r
  else if headCoefficient i r < 0 then negativeGuard i r
  else nonnegative (r.1, remainingOccurrences i r)

/-- The actual accepted constant residue at the literal positive modulus;
parameter term codes remain tied and are never evaluated or existentialized. -/
def residueRow (modulusMinusOne i : Nat) (r : RowData) : RowData :=
  ((WindowCode.add r.1.1 (WindowCode.multiply (headCoefficient i r).toNat
      (WindowCode.numeral (fastControlResidue (modulusMinusOne + 1)))),
    WindowCode.add r.1.2 (WindowCode.multiply (-(headCoefficient i r)).toNat
      (WindowCode.numeral (fastControlResidue (modulusMinusOne + 1))))),
    remainingOccurrences i r)
def residueAtom (modulusMinusOne i : Nat) (r : RowData) : Nat :=
  divisible modulusMinusOne (residueRow modulusMinusOne i r)

/-- A syntax-only charge. Nonzero malformed atom tags follow the original
all-code divisible branch; valid source tags remain exactly zero and one. -/
def atomCharge (a : AtomData) : Nat := 4 * mass a.2.2 + if a.1 = 0 then 0 else a.2.1 + 1
def cutoff (code : Nat) : Nat :=
  1 + ((LinearRows.Code.atoms code).map (fun a =>
    atomCharge (BlockFormulaSubstitutionCode.decodeAtom a))).sum

def lowerGuard (i c : Nat) : Nat :=
  nonnegative ((WindowCode.numeral 0, WindowCode.numeral c), [(1, TiedLinearCode.variableItem i)])
def strictMaximumGuard (i j : Nat) : Nat :=
  nonnegative ((WindowCode.numeral 0, WindowCode.numeral 1),
    [(1, TiedLinearCode.variableItem i), (-1, TiedLinearCode.variableItem j)])
def frame (bound : List Nat) (i code : Nat) : Nat :=
  conjunction (lowerGuard i (cutoff code))
    (all ((bound.filter (fun j => j != i)).map (strictMaximumGuard i)))

def outsideRow (i : Nat) (r : RowData) : Nat :=
  if headCoefficient i r = 0 then 0 else
    disjunction
      (nonnegative ((WindowCode.subtract (boundary i r) (WindowCode.numeral 2), WindowCode.numeral 1),
        [(-1, TiedLinearCode.variableItem i)]))
      (nonnegative ((WindowCode.numeral 0, WindowCode.add (boundary i r) (WindowCode.numeral 3)),
        [(1, TiedLinearCode.variableItem i)]))
def outside (i code : Nat) : Nat :=
  all ((LinearRows.Code.atoms code).map (fun payload =>
    let a := BlockFormulaSubstitutionCode.decodeAtom payload
    if a.1 = 0 then outsideRow i a.2.2 else 0))
def bandCandidate (i : Nat) (r : RowData) (d : Nat) : Nat :=
  WindowCode.add (WindowCode.subtract (boundary i r) (WindowCode.numeral 2)) (WindowCode.numeral d)

def linearizeAtom (i : Nat) (a : AtomData) : Nat :=
  if a.1 = 0 then linearizeNonnegative i a.2.2 else residueAtom a.2.1 i a.2.2

/-- Literal formula-valued atom replacement. Unlike mapAtoms, the atom branch
returns a complete formula code. The unchanged radix-six structural parsing,
Boolean positions and fixed block-atom decode fallback apply to every Nat. -/
def linearize (i : Nat) (code : Nat) : Nat :=
  if code % 6 = 0 then 0 else if code % 6 = 1 then 1
  else if code % 6 = 2 then linearizeAtom i (BlockFormulaSubstitutionCode.decodeAtom (code / 6))
  else if code % 6 = 3 then 6 * linearize i (code / 6) + 3
  else 6 * Nat.pair (linearize i (code / 6).unpair.1)
    (linearize i (code / 6).unpair.2) + code % 6
termination_by code
decreasing_by
  all_goals
    have hpos : 0 < code := by omega
    have hd : code / 6 < code := Nat.div_lt_self hpos (by decide)
    have hl := Nat.unpair_left_le (code / 6)
    have hr := Nat.unpair_right_le (code / 6)
    omega

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockLinearizationCode
