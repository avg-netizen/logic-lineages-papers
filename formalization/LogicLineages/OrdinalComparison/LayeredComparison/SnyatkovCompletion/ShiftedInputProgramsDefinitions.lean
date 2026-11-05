module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ShiftedInputGuardsDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.CommonHeadCodeDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ShiftedInputPrograms
open NormalForm ShiftedInputGuards

namespace Code
def varData (i : Nat) : NormalForm.Code.ItemData := (0, i, 0, 0)
def atom (r : NormalForm.Code.RowData) : Nat :=
  6 * Encodable.encode ((0, 0, r) : NormalForm.Code.AtomData) + 2
def negative (p : Nat) : Nat := 6 * p + 3
def conjunction (p q : Nat) : Nat := 6 * Nat.pair p q + 4
def disjunction (p q : Nat) : Nat := 6 * Nat.pair p q + 5

def less (a b : Input) : Nat :=
  conjunction (atom (b.2 - 1, [(1, varData b.1)]))
    (atom (b.2 - a.2 - 1, [(1, varData b.1), (-1, varData a.1)]))
def equal (a b : Input) : Nat := conjunction (negative (less a b)) (negative (less b a))
def bound (c : Nat) (a : Input) : Nat :=
  if c = 0 then 0 else atom (a.2 - (c : Int), [(1, varData a.1)])

/-- Total stack lowering of the existing literal postfix guard code. Invalid
programs receive fixed stack defaults; calibration is only for actual encodings. -/
def step (inputs : List Input) (stack : List Nat) (ins : CommonHeadCompiler.Instruction) : List Nat :=
  if ins.1 = 0 then 1 :: stack
  else if ins.1 = 1 then 0 :: stack
  else if ins.1 = 2 then equal (inputs.getD ins.2.1 (0, 0)) (inputs.getD ins.2.2 (0, 0)) :: stack
  else if ins.1 = 3 then less (inputs.getD ins.2.1 (0, 0)) (inputs.getD ins.2.2 (0, 0)) :: stack
  else if ins.1 = 4 then bound ins.2.1 (inputs.getD ins.2.2 (0, 0)) :: stack
  else if ins.1 = 5 then negative (stack.getD 0 1) :: stack.drop 1
  else if ins.1 = 6 then conjunction (stack.getD 1 1) (stack.getD 0 1) :: stack.drop 2
  else disjunction (stack.getD 1 1) (stack.getD 0 1) :: stack.drop 2

def run (inputs : List Input) (code : CommonHeadCode.Code) (stack : List Nat) : List Nat :=
  code.foldl (step inputs) stack
def compile (inputs : List Input) (code : CommonHeadCode.Code) : Nat := (run inputs code []).getD 0 1

def occurrences (r : NormalForm.Code.RowData) : List (Int × Input) :=
  (r.2.filter (fun a => a.2.1 == 1)).map (fun a => (a.1, a.2.2.1, a.2.2.2.1))
def coefficients (r : NormalForm.Code.RowData) : List Int := (occurrences r).map Prod.fst
def inputs (r : NormalForm.Code.RowData) : List Input := (occurrences r).map Prod.snd

def canceled (r : NormalForm.Code.RowData) : Nat :=
  compile (inputs r) (CommonHeadCode.canceledCode (coefficients r))
def block (r : NormalForm.Code.RowData) (k : Nat) (desired : Int) : Nat :=
  compile (inputs r) (CommonHeadCode.blockCode (coefficients r) k desired)
def activeSign (r : NormalForm.Code.RowData) (desired : Int) : Nat :=
  compile (inputs r) (CommonHeadCode.signCode 0 (coefficients r) desired)
end Code

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ShiftedInputPrograms
