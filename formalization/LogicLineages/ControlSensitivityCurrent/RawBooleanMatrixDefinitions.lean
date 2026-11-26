module
public import LogicLineages.ControlSensitivityCurrent.RawBinaryPlanDefinitions
public import LogicLineages.OrdinalComparison.SourceBooleanPlanDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG.BooleanMatrix

open LogicLineages.OrdinalComparison.Source
open BinaryPlanCompiler (binder gate shiftPort)
open PrimitiveGate (GateCode)

abbrev RowCode := Nat × Nat × Nat

def encodeRow {n m : Nat} : BooleanWire.Node n m → RowCode
  | .eq a b => (0,a.val,b.val)
  | .le a b => (1,a.val,b.val)
  | .lt a b => (2,a.val,b.val)
  | .neg a => (3,a.val,0)
  | .conj a b => (4,a.val,b.val)
  | .disj a b => (5,a.val,b.val)

def encodeRows {n : Nat} : {m : Nat} → BooleanWire.Dag n m → List RowCode
  | _, .nil => []
  | _, .snoc d row => encodeRow row :: encodeRows d

def eqCode (a b : Nat) : GateCode := (0,a,b,0,0)
def addCode (a b c : Nat) : GateCode := (1,a,b,c,0)
def sortCode (a b l h : Nat) : GateCode := (2,a,b,l,h)

def bitCode (i : Nat) : Nat := 9*i+1
def auxiliaryCode (i j : Nat) : Nat := 9*i+j+2
def oneCode (m : Nat) : Nat := 9*m+1

/-- The codes of the actual local constraint list at one global node position. -/
def localRaw (m : Nat) (ports : List Nat) (i : Nat) (row : RowCode) : List GateCode :=
  let (tag,a,b) := row
  let x := shiftPort (oneCode m) (ports.getD a 0)
  let y := shiftPort (oneCode m) (ports.getD b 0)
  let priorA := bitCode (i+a+1)
  let priorB := bitCode (i+b+1)
  let out := bitCode i
  let z := auxiliaryCode i
  let one := oneCode m
  if tag = 0 then
    [sortCode x y (z 0) (z 1), addCode (z 0) (z 2) (z 1),
      sortCode (z 2) one (z 3) (z 4), addCode out (z 3) one,
      eqCode (z 5) 0, eqCode (z 6) 0, eqCode (z 7) 0]
  else if tag = 1 then
    [sortCode x y (z 0) (z 1), sortCode (z 1) y (z 2) (z 3),
      addCode (z 2) (z 4) (z 3), sortCode (z 4) one (z 5) (z 6),
      addCode out (z 5) one, eqCode (z 7) 0]
  else if tag = 2 then
    [sortCode y x (z 0) (z 1), sortCode (z 1) x (z 2) (z 3),
      addCode (z 2) (z 4) (z 3), sortCode (z 4) one (z 5) (z 6),
      addCode (z 7) (z 5) one, addCode out (z 7) one]
  else if tag = 3 then
    addCode out priorA one :: (List.range 8).map (fun j => eqCode (z j) 0)
  else if tag = 4 then
    [sortCode priorA priorB (z 0) (z 1), eqCode out (z 0),
      eqCode (z 2) 0, eqCode (z 3) 0, eqCode (z 4) 0,
      eqCode (z 5) 0, eqCode (z 6) 0, eqCode (z 7) 0]
  else
    [sortCode priorA priorB (z 0) (z 1), eqCode out (z 1),
      eqCode (z 2) 0, eqCode (z 3) 0, eqCode (z 4) 0,
      eqCode (z 5) 0, eqCode (z 6) 0, eqCode (z 7) 0]

abbrev RowState := Nat × List GateCode

def emitRow (m : Nat) (ports : List Nat) (state : RowState) (row : RowCode) : RowState :=
  (state.1-1,state.2 ++ localRaw m ports (state.1-1) row)

def emitRows (m : Nat) (ports : List Nat) (offset : Nat) (rows : List RowCode) : RowState :=
  rows.reverse.foldl (emitRow m ports) (offset + rows.length,[])

/-- Context and reference checks belong to the raw frontend that constructs these tables. -/
def matrixRaw (ports : List Nat) (rows : List RowCode) (root : Nat) : List PlanCompiler.Instruction :=
  let m := rows.length
  let gates := (3,oneCode m,0,0,0) :: (emitRows m ports 0 rows).2 ++ [eqCode (bitCode root) (oneCode m)]
  List.replicate (oneCode m) binder ++ gates.map gate

end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.BooleanMatrix
