module
public import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.Definitions
public import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.OrdinalComparison.PolynomialGraphCompletion

/-- The printed fixed nesting/addition grammar, including natural constants
and fixed natural multiples. Collapse payloads are literal closed head codes;
ValidExpr requires every one to be a genuine nonzero polynomial limit. -/
inductive Expr where
  | numeral (n : Nat)
  | variable (i : Nat)
  | add (left right : Expr)
  | scale (coefficient : Nat) (input : Expr)
  | collapse (headCode : Nat) (input : Expr)

noncomputable def Expr.value (ν : Nat → Nat) : Expr → Nat
  | .numeral n => n
  | .variable i => ν i
  | .add a b => a.value ν + b.value ν
  | .scale k a => k * a.value ν
  | .collapse code a => headValue code (a.value ν)

def Expr.variables : Expr → List Nat
  | .numeral _ => []
  | .variable i => [i]
  | .add a b => a.variables ++ b.variables
  | .scale _ a | .collapse _ a => a.variables

/-- Head occurrences retain postfix order and repetitions. A finite maximum
degree is computed from this exact finite collection. -/
def Expr.heads : Expr → List Nat
  | .numeral _ | .variable _ => []
  | .add a b => a.heads ++ b.heads
  | .scale _ a => a.heads
  | .collapse code a => a.heads ++ [code]

noncomputable def ValidExpr (t : Expr) : Prop :=
  ∀ code ∈ t.heads, ValidHead code

def exprDegree (t : Expr) : Nat := familyDegree t.heads

def Expr.encode : Expr → Nat
  | .numeral n => 5 * n
  | .variable i => 5 * i + 1
  | .add a b => 5 * Nat.pair a.encode b.encode + 2
  | .scale k a => 5 * Nat.pair k a.encode + 3
  | .collapse code a => 5 * Nat.pair code a.encode + 4

/-- Every syntactic occurrence gets one fresh natural node variable. In
particular repeated original variable names remain linked to the same name. -/
def nodeCount : Expr → Nat
  | .numeral _ | .variable _ => 1
  | .add a b => nodeCount a + nodeCount b + 1
  | .scale _ a | .collapse _ a => nodeCount a + 1

def names (start count : Nat) : List Nat := (List.range count).map (start + ·)
def allocated (start : Nat) (t : Expr) : List Nat := names start (nodeCount t)
def output (start : Nat) (t : Expr) : Nat := start + nodeCount t - 1
def Fresh (start : Nat) (t : Expr) : Prop := ∀ i ∈ t.variables, i < start

/-- The symbolic result name is included even if it already occurs in the
source expression. Only the newly allocated node names are quantified. -/
def freshStart (t : Expr) (resultName : Nat) : Nat :=
  1 + max resultName (t.variables.foldr max 0)

def numeralRow (z n : Nat) : Row := (-(n : Int),[(1,z,[])])
def variableRow (z i : Nat) : Row := (0,[(1,z,[]),(-1,i,[])])
def additionRow (z x y : Nat) : Row := (0,[(1,z,[]),(-1,x,[]),(-1,y,[])])
def scaleRow (z k x : Nat) : Row := (0,[(1,z,[]),(-(k : Int),x,[])])

/-- Literal postorder equations. A collapse is applied to its child's node
name, never to a sum of word values or to an independent surrogate input. -/
def rows (start : Nat) : Expr → List Row
  | .numeral n => [numeralRow start n]
  | .variable i => [variableRow start i]
  | .add a b =>
      rows start a ++ rows (start + nodeCount a) b ++
        [additionRow (output start (.add a b)) (output start a)
          (output (start + nodeCount a) b)]
  | .scale k a => rows start a ++
      [scaleRow (output start (.scale k a)) k (output start a)]
  | .collapse code a => rows start a ++
      [headEquation code (output start a) (output start (.collapse code a))]

noncomputable def RowsHold (rs : List Row) (ν : Nat → Nat) : Prop :=
  ∀ row ∈ rs, RowDomain row ν ∧ RowValue row ν = 0

noncomputable def GraphHolds (start : Nat) (t : Expr) (ν : Nat → Nat) : Prop :=
  RowsHold (rows start t) ν

def graphRows (t : Expr) (resultName : Nat) : List Row :=
  rows (freshStart t resultName) t ++
    [variableRow resultName (output (freshStart t resultName) t)]

abbrev ExpressionPackage := Nat × List Nat × List Row

/-- The finite artifact includes its degree bound, its entire natural
existential prefix, and the literal word-linear equations. -/
def expressionPackage (t : Expr) (resultName : Nat) : ExpressionPackage :=
  (exprDegree t,allocated (freshStart t resultName) t,graphRows t resultName)

/-- Exactly one natural existential quantifier per listed node. Original
names, including the requested result name, remain free and correlated. -/
noncomputable def existsNodes (ν : Nat → Nat) : List Nat → List Row → Prop
  | [], rs => RowsHold rs ν
  | i :: is, rs => ∃ n : Nat, existsNodes (Function.update ν i n) is rs

noncomputable def expressionGraph (t : Expr) (resultName : Nat) (ν : Nat → Nat) : Prop :=
  existsNodes ν (expressionPackage t resultName).2.1 (expressionPackage t resultName).2.2

abbrev Instruction := Nat × Nat

def instructions : Expr → List Instruction
  | .numeral n => [(0,n)]
  | .variable i => [(1,i)]
  | .add a b => instructions a ++ instructions b ++ [(2,0)]
  | .scale k a => instructions a ++ [(3,k)]
  | .collapse code a => instructions a ++ [(4,code)]

namespace ExpressionCode
abbrev State := Nat × List Nat × List Row

def originalNames (ops : List Instruction) : List Nat :=
  (ops.filter (fun op => decide (op.1 = 1))).map Prod.snd
def headNames (ops : List Instruction) : List Nat :=
  (ops.filter (fun op => decide (op.1 = 4))).map Prod.snd
def start (ops : List Instruction) (resultName : Nat) : Nat :=
  1 + max resultName ((originalNames ops).foldr max 0)

def emit (s : State) (tail : List Nat) (row : Row) : State :=
  (s.1+1,s.1::tail,s.2.2++[row])

def step (s : State) (op : Instruction) : State :=
  if op.1 = 0 then emit s s.2.1 (numeralRow s.1 op.2)
  else if op.1 = 1 then emit s s.2.1 (variableRow s.1 op.2)
  else if op.1 = 2 then emit s (s.2.1.drop 2)
    (additionRow s.1 (s.2.1.getD 1 0) (s.2.1.getD 0 0))
  else if op.1 = 3 then emit s (s.2.1.drop 1)
    (scaleRow s.1 op.2 (s.2.1.getD 0 0))
  else emit s (s.2.1.drop 1) (headEquation op.2 (s.2.1.getD 0 0) s.1)

def run (ops : List Instruction) (s : State) : State := ops.foldl step s

/-- All five radix branches are explicit. Nested head codes and arithmetic
payloads are source data; only expression children are recursively parsed. -/
def instructions (code : Nat) : List Instruction :=
  if code % 5 = 0 then [(0,code/5)]
  else if code % 5 = 1 then [(1,code/5)]
  else if code % 5 = 2 then
    instructions (code/5).unpair.1 ++ instructions (code/5).unpair.2 ++ [(2,0)]
  else if code % 5 = 3 then instructions (code/5).unpair.2 ++ [(3,(code/5).unpair.1)]
  else instructions (code/5).unpair.2 ++ [(4,(code/5).unpair.1)]
termination_by code
decreasing_by
  all_goals
    have hpos : 0 < code := by omega
    have hd : code/5 < code := Nat.div_lt_self hpos (by decide)
    have hl := Nat.unpair_left_le (code/5)
    have hr := Nat.unpair_right_le (code/5)
    omega

def package (code resultName : Nat) : ExpressionPackage :=
  let ops := instructions code
  let first := start ops resultName
  let s := run ops (first,[],[])
  (familyDegree (headNames ops),names first ops.length,
    s.2.2++[variableRow resultName (s.1-1)])

end ExpressionCode
end LogicLineages.OrdinalComparison.PolynomialGraphCompletion
