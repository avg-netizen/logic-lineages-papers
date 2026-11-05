module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NormalFormDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceTermGraph
open CommonLayerSyntax NormalForm

/-- One fresh name for every source occurrence, including variable leaves. -/
def nodeCount : BaseTerm → Nat
  | .numeral _ | .variable _ => 1
  | .add a b => nodeCount a + nodeCount b + 1
  | .phi a => nodeCount a + 1

def names (start count : Nat) : List Nat := (List.range count).map (start + ·)
def allocated (start : Nat) (t : BaseTerm) : List Nat := names start (nodeCount t)
def output (start : Nat) (t : BaseTerm) : Nat := start + nodeCount t - 1
def Fresh (start : Nat) (t : BaseTerm) : Prop := ∀ i ∈ t.variables, i < start

def numeralRow (z n : Nat) : Row := (-(n : Int), [(1, .variable z)])
def variableRow (z i : Nat) : Row := (0, [(1, .variable z), (-1, .variable i)])
def additionRow (z x y : Nat) : Row :=
  (0, [(1, .variable z), (-1, .variable x), (-1, .variable y)])
def phiRow (z x : Nat) : Row := (0, [(1, .variable z), (-1, .phi x 0)])

def negateRow (row : Row) : Row := (-row.1, row.2.map (fun a => (-a.1, a.2)))
def equation (row : Row) : NormalForm.Formula :=
  .conjunction (.atom (.nonnegative row)) (.atom (.nonnegative (negateRow row)))
def equations (rows : List Row) : NormalForm.Formula :=
  rows.foldr (fun row rest => .conjunction (equation row) rest) .truth

/-- Literal postorder graph. Original variable indices are never renamed. -/
def rows (start : Nat) : BaseTerm → List Row
  | .numeral n => [numeralRow start n]
  | .variable i => [variableRow start i]
  | .add a b =>
      rows start a ++ rows (start + nodeCount a) b ++
        [additionRow (output start (.add a b)) (output start a)
          (output (start + nodeCount a) b)]
  | .phi a => rows start a ++ [phiRow (output start (.phi a)) (output start a)]

def graph (start : Nat) (t : BaseTerm) : NormalForm.Formula := equations (rows start t)
def resultFormula (start : Nat) (t : BaseTerm) (y : Nat) : NormalForm.Formula :=
  .conjunction (graph start t) (equation (numeralRow (output start t) y))

/-- Postfix source occurrences; addition consumes the two top stack results. -/
abbrev Instruction := Nat × Nat
def instructions : BaseTerm → List Instruction
  | .numeral n => [(0, n)]
  | .variable i => [(1, i)]
  | .add a b => instructions a ++ instructions b ++ [(2, 0)]
  | .phi a => instructions a ++ [(3, 0)]

namespace Code
abbrev RowData := NormalForm.Code.RowData
abbrev State := Nat × (List Nat × List RowData)

def variableData (i : Nat) : NormalForm.Code.ItemData := (0, i, 0, 0)
def phiData (i : Nat) : NormalForm.Code.ItemData := (1, i, 0, 0)
def numeralRow (z n : Nat) : RowData := (-(n : Int), [(1, variableData z)])
def variableRow (z i : Nat) : RowData := (0, [(1, variableData z), (-1, variableData i)])
def additionRow (z x y : Nat) : RowData :=
  (0, [(1, variableData z), (-1, variableData x), (-1, variableData y)])
def phiRow (z x : Nat) : RowData := (0, [(1, variableData z), (-1, phiData x)])
def negateRow (row : RowData) : RowData := (-row.1, row.2.map (fun a => (-a.1, a.2)))

def atom (row : RowData) : Nat :=
  6 * Encodable.encode ((0, 0, row) : NormalForm.Code.AtomData) + 2
def conjunction (a b : Nat) : Nat := 6 * Nat.pair a b + 4
def equation (row : RowData) : Nat := conjunction (atom row) (atom (negateRow row))
def equations (rows : List RowData) : Nat :=
  rows.foldr (fun row rest => conjunction (equation row) rest) 0

def emit (s : State) (tail : List Nat) (row : RowData) : State :=
  (s.1 + 1, s.1 :: tail, s.2.2 ++ [row])
def step (s : State) (op : Instruction) : State :=
  if op.1 = 0 then emit s s.2.1 (numeralRow s.1 op.2)
  else if op.1 = 1 then emit s s.2.1 (variableRow s.1 op.2)
  else if op.1 = 2 then emit s (s.2.1.drop 2)
    (additionRow s.1 (s.2.1.getD 1 0) (s.2.1.getD 0 0))
  else emit s (s.2.1.drop 1) (phiRow s.1 (s.2.1.getD 0 0))
def run (ops : List Instruction) (s : State) : State := ops.foldl step s

/-- Total source-code compiler. All four radix-4 branches are explicit. -/
def instructions (code : Nat) : List Instruction :=
  if code % 4 = 0 then [(0, code / 4)]
  else if code % 4 = 1 then [(1, code / 4)]
  else if code % 4 = 2 then
    instructions (code / 4).unpair.1 ++ instructions (code / 4).unpair.2 ++ [(2, 0)]
  else instructions (code / 4) ++ [(3, 0)]
termination_by code
decreasing_by
  all_goals
    have hpos : 0 < code := by omega
    have hd : code / 4 < code := Nat.div_lt_self hpos (by decide)
    have hl := Nat.unpair_left_le (code / 4)
    have hr := Nat.unpair_right_le (code / 4)
    omega

/-- The returned natural codes the actual output name and row formula code. -/
def package (code start : Nat) : Nat :=
  let s := run (instructions code) (start, [], [])
  Encodable.encode (s.1 - 1, equations s.2.2)
end Code

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceTermGraph
