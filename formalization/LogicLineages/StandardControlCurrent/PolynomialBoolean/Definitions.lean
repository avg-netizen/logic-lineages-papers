module
public import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.ExpressionDefinitions
public import LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.Definitions
public import LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.MachineDefinitions

@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolynomialBoolean
open OrdinalComparison PolynomialGraphCompletion

inductive Relation where
  | equal | weak | strict
  deriving DecidableEq

def Relation.code : Relation → Nat
  | .equal => 0 | .weak => 1 | .strict => 2

inductive Source where
  | truth (b : Bool)
  | atom (r : Relation) (left right : Expr)
  | neg (p : Source)
  | conj (p q : Source)
  | disj (p q : Source)

noncomputable def Source.Valid (d : Nat) : Source → Prop
  | .truth _ => True
  | .atom _ a b => ValidExpr a ∧ ValidExpr b ∧
      (∀ i ∈ a.variables, i < d) ∧ (∀ i ∈ b.variables, i < d)
  | .neg p => p.Valid d
  | .conj p q | .disj p q => p.Valid d ∧ q.Valid d

noncomputable def Source.eval (ν : Nat → Nat) : Source → Prop
  | .truth b => b = true
  | .atom .equal a b => a.value ν = b.value ν
  | .atom .weak a b => a.value ν ≤ b.value ν
  | .atom .strict a b => a.value ν < b.value ν
  | .neg p => ¬p.eval ν
  | .conj p q => p.eval ν ∧ q.eval ν
  | .disj p q => p.eval ν ∨ q.eval ν

def Source.heads : Source → List Nat
  | .truth _ => []
  | .atom _ a b => a.heads ++ b.heads
  | .neg p => p.heads
  | .conj p q | .disj p q => p.heads ++ q.heads

def Source.degree (p : Source) : Nat := familyDegree p.heads

def negativeRow (r : Row) : Row := (-r.1, r.2.map fun a => (-a.1,a.2))
def equality (r : Row) : WordLinearDecisionCompletion.Formula :=
  .conj (.atom (.nonnegative r)) (.atom (.nonnegative (negativeRow r)))
def relationRow (strict : Bool) (left right : Nat) : Row :=
  (if strict then -1 else 0, [(1,right,[]),(-1,left,[])])
def outputTest (r : Relation) (left right : Nat) : WordLinearDecisionCompletion.Formula :=
  match r with
  | .equal => equality (relationRow false left right)
  | .weak => .atom (.nonnegative (relationRow false left right))
  | .strict => .atom (.nonnegative (relationRow true left right))

abbrev Artifact := Nat × List Row × WordLinearDecisionCompletion.Formula
/-- All graphs remain positive; only the final output formula follows Boolean structure. -/
def compile (start : Nat) : Source → Artifact
  | .truth b => (start,[],if b then .top else .bot)
  | .atom r a b =>
      let next := start + nodeCount a
      (next + nodeCount b, rows start a ++ rows next b,
        outputTest r (output start a) (output next b))
  | .neg p => let a := compile start p; (a.1,a.2.1,.neg a.2.2)
  | .conj p q =>
      let a := compile start p; let b := compile a.1 q
      (b.1,a.2.1++b.2.1,.conj a.2.2 b.2.2)
  | .disj p q =>
      let a := compile start p; let b := compile a.1 q
      (b.1,a.2.1++b.2.1,.disj a.2.2 b.2.2)

def graphFormula (rs : List Row) : WordLinearDecisionCompletion.Formula := rs.foldr (fun r q => .conj (equality r) q) .top
def positiveFormula (d : Nat) : WordLinearDecisionCompletion.Formula :=
  (List.range d).foldr (fun i q => .conj (.atom (.nonnegative (-1,[(1,i,[])]))) q) .top
def matrix (d : Nat) (p : Source) (counterexample : Bool) : WordLinearDecisionCompletion.Formula :=
  let a := compile d p
  .conj (positiveFormula d) (.conj (graphFormula a.2.1)
    (if counterexample then .neg a.2.2 else a.2.2))

def Positive (d : Nat) (ν : Nat → Nat) : Prop := ∀ i, i < d → 0 < ν i

abbrev Instruction := Nat × Nat × Nat
/-- Actual literal postfix compiler. Atom operands are unchanged expression codes. -/
def program : Source → List Instruction
  | .truth b => [(if b then 1 else 0,0,0)]
  | .atom r a b => [(2+r.code,a.encode,b.encode)]
  | .neg p => program p ++ [(5,0,0)]
  | .conj p q => program p ++ program q ++ [(6,0,0)]
  | .disj p q => program p ++ program q ++ [(7,0,0)]
def sourceCode (p : Source) : Nat := Encodable.encode (program p)

namespace Code
abbrev State := Nat × List Row × List Nat

def nonnegative (r : Row) : Nat := 6 * Encodable.encode ((0,0,r) : WordLinearDecisionCompletion.Code.AtomData) + 2
def neg (p : Nat) : Nat := 6*p+3
def conj (p q : Nat) : Nat := 6*Nat.pair p q+4
def disj (p q : Nat) : Nat := 6*Nat.pair p q+5
def equal (r : Row) : Nat := conj (nonnegative r) (nonnegative (negativeRow r))
def test (r left right : Nat) : Nat :=
  if r=0 then equal (relationRow false left right)
  else nonnegative (relationRow (r != 1) left right)

def step (s : State) (op : Instruction) : State :=
  if op.1 ≤ 1 then (s.1,s.2.1,(if op.1=1 then 0 else 1)::s.2.2)
  else if op.1 ≤ 4 then
    let a := ExpressionCode.run (ExpressionCode.instructions op.2.1) (s.1,[],[])
    let b := ExpressionCode.run (ExpressionCode.instructions op.2.2) (a.1,[],[])
    (b.1,s.2.1++a.2.2++b.2.2,test (op.1-2) (a.2.1.headD 0) (b.2.1.headD 0)::s.2.2)
  else if op.1=5 then (s.1,s.2.1,neg (s.2.2.headD 1)::s.2.2.tail)
  else if op.1=6 then (s.1,s.2.1,conj (s.2.2.getD 1 1) (s.2.2.headD 1)::s.2.2.drop 2)
  else (s.1,s.2.1,disj (s.2.2.getD 1 1) (s.2.2.headD 1)::s.2.2.drop 2)

def decode (code : Nat) : List Instruction := (Encodable.decode code).getD []
def heads (ops : List Instruction) : List Nat := ops.flatMap fun op =>
  if 2 ≤ op.1 ∧ op.1 ≤ 4 then
    ExpressionCode.headNames (ExpressionCode.instructions op.2.1) ++
    ExpressionCode.headNames (ExpressionCode.instructions op.2.2)
  else []
def graph (rs : List Row) : Nat := rs.foldr (fun r q => conj (equal r) q) 0
def positive (d : Nat) : Nat :=
  (List.range d).foldr (fun i q => conj (nonnegative (-1,[(1,i,[])])) q) 0
/-- degree,next-name,existential matrix code,counterexample matrix code -/
def package (d code : Nat) : Nat × Nat × Nat × Nat :=
  let ops := decode code
  let s := ops.foldl step (d,[],[])
  let out := s.2.2.headD 1
  (familyDegree (heads ops),s.1,conj (positive d) (conj (graph s.2.1) out),
    conj (positive d) (conj (graph s.2.1) (neg out)))

noncomputable def flags (d code : Nat) : Bool × Bool :=
  let a := package d code
  (ClosedWordDecisionCompletion.Machine.solve a.1 a.2.2.1,
   !(ClosedWordDecisionCompletion.Machine.solve a.1 a.2.2.2))
end Code
end LogicLineages.StandardControlCurrent.PolynomialBoolean
