module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceTermGraphDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceRows
open CommonLayerSyntax NormalForm SourceTermGraph

/-- Quantified row syntax. Original Boolean operators and named binders remain
in place; this is the introduction stage, before quantifier elimination. -/
inductive QFormula where
  | matrix (body : NormalForm.Formula)
  | negative (body : QFormula)
  | conjunction (left right : QFormula)
  | existsNat (name : Nat) (body : QFormula)

def QFormula.eval (ν : Nat → Nat) : QFormula → Prop
  | .matrix p => p.eval ν
  | .negative p => ¬p.eval ν
  | .conjunction p q => p.eval ν ∧ q.eval ν
  | .existsNat i p => ∃ n : Nat, p.eval (Function.update ν i n)

def QFormula.variables : QFormula → List Nat
  | .matrix p => p.variables
  | .negative p => p.variables
  | .conjunction p q => p.variables ++ q.variables
  | .existsNat i p => p.variables.filter (fun j => j != i)

def QFormula.encode : QFormula → Nat
  | .matrix p => 4 * p.encode
  | .negative p => 4 * p.encode + 1
  | .conjunction p q => 4 * Nat.pair p.encode q.encode + 2
  | .existsNat i p => 4 * Nat.pair i p.encode + 3

def bindAll (xs : List Nat) (p : QFormula) : QFormula :=
  xs.foldr QFormula.existsNat p

namespace Code
def opBound (op : SourceTermGraph.Instruction) : Nat :=
  if op.1 = 1 then op.2 + 1 else 0
def bound (ops : List SourceTermGraph.Instruction) : Nat :=
  (ops.map opBound).foldr max 0
end Code

/-- The atom's original names, including occurrences bound by an enclosing
source quantifier, lie below this local starting name. -/
def localStart (a b : BaseTerm) : Nat :=
  max (Code.bound (SourceTermGraph.instructions a))
    (Code.bound (SourceTermGraph.instructions b))

def strictRow (x y : Nat) : Row :=
  (-1, [(1, .variable y), (-1, .variable x)])
def relation (strict : Bool) (x y : Nat) : NormalForm.Formula :=
  if strict then .atom (.nonnegative (strictRow x y))
  else equation (variableRow x y)

/-- A joined term graph records both operands and one final sum slot. The
comparison uses the two child outputs, not the sum output. -/
def atomBody (strict : Bool) (a b : BaseTerm) : NormalForm.Formula :=
  let start := localStart a b
  .conjunction (graph start (.add a b))
    (relation strict (output start a) (output (start + nodeCount a) b))

/-- Every introduced witness is local to this source atom. No witness binder
is moved across a source negation or source binder. -/
def localAtom (strict : Bool) (a b : BaseTerm) : QFormula :=
  bindAll (allocated (localStart a b) (.add a b)) (.matrix (atomBody strict a b))

def translate : SourceFormula → QFormula
  | .equal a b => localAtom false a b
  | .less a b => localAtom true a b
  | .negative p => .negative (translate p)
  | .conjunction p q => .conjunction (translate p) (translate q)
  | .existsNat i p => .existsNat i (translate p)

namespace Code
def bindAll (xs : List Nat) (body : Nat) : Nat :=
  xs.foldr (fun i rest => 4 * Nat.pair i rest + 3) body

def strictRow (x y : Nat) : NormalForm.Code.RowData :=
  (-1, [(1, SourceTermGraph.Code.variableData y),
    (-1, SourceTermGraph.Code.variableData x)])
def relation (strict : Bool) (x y : Nat) : Nat :=
  if strict then SourceTermGraph.Code.atom (strictRow x y)
  else SourceTermGraph.Code.equation (SourceTermGraph.Code.variableRow x y)

/-- Actual numeric atom compiler, including allocation, graph execution,
comparison and the complete list of local existential binders. -/
def atom (strict : Bool) (a b : Nat) : Nat :=
  let ia := SourceTermGraph.Code.instructions a
  let ib := SourceTermGraph.Code.instructions b
  let start := max (bound ia) (bound ib)
  let s := SourceTermGraph.Code.run
    (SourceTermGraph.Code.instructions (4 * Nat.pair a b + 2)) (start, [], [])
  let body := SourceTermGraph.Code.conjunction
    (SourceTermGraph.Code.equations s.2.2)
    (relation strict (start + ia.length - 1) (start + ia.length + ib.length - 1))
  bindAll (SourceTermGraph.names start (ia.length + ib.length + 1)) (4 * body)

/-- Total radix-5 source compiler. Original binder indices are copied literally. -/
def translate (code : Nat) : Nat :=
  if code % 5 = 0 then atom false (code / 5).unpair.1 (code / 5).unpair.2
  else if code % 5 = 1 then atom true (code / 5).unpair.1 (code / 5).unpair.2
  else if code % 5 = 2 then 4 * translate (code / 5) + 1
  else if code % 5 = 3 then
    4 * Nat.pair (translate (code / 5).unpair.1) (translate (code / 5).unpair.2) + 2
  else 4 * Nat.pair (code / 5).unpair.1 (translate (code / 5).unpair.2) + 3
termination_by code
decreasing_by
  all_goals
    have hpos : 0 < code := by omega
    have hd : code / 5 < code := Nat.div_lt_self hpos (by decide)
    have hl := Nat.unpair_left_le (code / 5)
    have hr := Nat.unpair_right_le (code / 5)
    omega
end Code

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceRows
