module
public import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.ExpressionDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LevelTwoCounterexample.Pair
open PolynomialGraphCompletion

/-- Source comparison modes: weak, WW-strict scalar, equality. Positive
coordinate comparison is supplied separately as the actual closed flag. -/
def valueRelation (mode a b : Nat) : Prop :=
  if mode = 0 then a ≤ b else if mode = 1 then a < b else a = b

/-- The literal failed comparison of the integer-linear difference a-b. -/
def badSign (mode : Nat) (z : Int) : Prop :=
  if mode = 0 then 0 < z else if mode = 1 then 0 ≤ z else z ≠ 0

def differenceRow (x y : Nat) : Row := (0,[(1,x,[]),(-1,y,[])])

/-- A finite natural existential prefix with its original binder order. -/
noncomputable def existsPrefix (ν : Nat → Nat) : List Nat → ((Nat → Nat) → Prop) → Prop
  | [], body => body ν
  | i::is, body => ∃ n : Nat, existsPrefix (Function.update ν i n) is body

/-- Degree and original arity, complete existential prefix, graph equations,
comparison row, comparison mode and the closed positive-coordinate flag. -/
abbrev Package := (Nat × Nat) × List Nat × List Row × Row × (Nat × Bool)

def package (n mode : Nat) (flag : Bool) (a b : Expr) : Package :=
  ((exprDegree (.add a b),n),List.range (n+nodeCount (.add a b)),
    rows n (.add a b),differenceRow (output n a) (output (n+nodeCount a) b),(mode,flag))

/-- The sum node is an auxiliary bookkeeping node in the existing graph
compiler. Only the two child outputs are tested; it is not a replacement of
comparison by comparison of independent values or by comparison of sums. -/
noncomputable def Matrix (p : Package) (ν : Nat → Nat) : Prop :=
  (∀ i < p.1.2, 0 < ν i) ∧ RowsHold p.2.2.1 ν ∧ RowDomain p.2.2.2.1 ν ∧
    (p.2.2.2.2.2 = false ∨ badSign p.2.2.2.2.1 (RowValue p.2.2.2.1 ν))

noncomputable def Closed (p : Package) : Prop :=
  existsPrefix (fun _ => 0) p.2.1 (Matrix p)

namespace Code
abbrev Input := Nat × Nat × Bool × Nat × Nat

def package (p : Input) : Package :=
  let left := ExpressionCode.instructions p.2.2.2.1
  let right := ExpressionCode.instructions p.2.2.2.2
  let ops := left++right++[(2,0)]
  let state := ExpressionCode.run ops (p.1,[],[])
  ((familyDegree (ExpressionCode.headNames ops),p.1),List.range (p.1+ops.length),
    state.2.2,differenceRow (p.1+left.length-1) (p.1+left.length+right.length-1),
      (p.2.1,p.2.2.1))
end Code
end LogicLineages.OrdinalComparison.LevelTwoCounterexample.Pair
