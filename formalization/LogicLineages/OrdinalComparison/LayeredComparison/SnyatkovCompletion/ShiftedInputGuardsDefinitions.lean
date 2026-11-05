module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainPhiDominanceDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsDefinitions
public import LogicLineages.OrdinalComparison.CommonHeadLargeGuardsDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ShiftedInputGuards
open NormalForm

/-- An original name and its literal signed input shift. -/
abbrev Input := Nat × Int
def value (a : Input) (ν : Nat → Nat) : Nat := ((ν a.1 : Int) + a.2).toNat

/-- Natural truncation is represented exactly, including negative signed inputs. -/
def less (a b : Input) : NormalForm.Formula :=
  .conjunction (.atom (.nonnegative (b.2 - 1, [(1, .variable b.1)])))
    (.atom (.nonnegative (b.2 - a.2 - 1, [(1, .variable b.1), (-1, .variable a.1)])))
def equal (a b : Input) : NormalForm.Formula :=
  .conjunction (.negative (less a b)) (.negative (less b a))
def bound (c : Nat) (a : Input) : NormalForm.Formula :=
  if c = 0 then .truth else .atom (.nonnegative (a.2 - (c : Int), [(1, .variable a.1)]))

def valuation (inputs : List Input) (ν : Nat → Nat) (i : Nat) : Nat :=
  value (inputs.getD i (0, 0)) ν

/-- All labels are replaced by their original signed-shifted inputs. The output
contains only linear source rows and retains one shared raw valuation. -/
def compile (inputs : List Input) : CommonHeadLargeGuards.Formula → NormalForm.Formula
  | .truth => .truth
  | .falsity => .falsity
  | .eq i j => equal (inputs.getD i (0, 0)) (inputs.getD j (0, 0))
  | .lt i j => less (inputs.getD i (0, 0)) (inputs.getD j (0, 0))
  | .bound c i => bound c (inputs.getD i (0, 0))
  | .neg p => .negative (compile inputs p)
  | .conj p q => .conjunction (compile inputs p) (compile inputs q)
  | .disj p q => .disjunction (compile inputs p) (compile inputs q)

/-- Keep every original Phi occurrence, including zero weights and repeated
names. Collection is not performed on this source list. -/
def occurrences (r : Row) : List (Int × Input) :=
  r.2.flatMap (fun a => match a.2 with
    | .phi i e => [(a.1, i, e)]
    | _ => [])
def coefficients (r : Row) : List Int := (occurrences r).map Prod.fst
def inputs (r : Row) : List Input := (occurrences r).map Prod.snd

def canceled (r : Row) : NormalForm.Formula :=
  compile (inputs r) (CommonHeadLargeGuards.canceledFormula (coefficients r))
def block (r : Row) (k : Nat) (desired : Int) : NormalForm.Formula :=
  compile (inputs r) (CommonHeadLargeGuards.blockFormula (coefficients r) k desired)
def activeSign (r : Row) (desired : Int) : NormalForm.Formula :=
  compile (inputs r) (CommonHeadLargeGuards.signFormula 0 (coefficients r) desired)

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ShiftedInputGuards
