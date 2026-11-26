module
public import LogicLineages.StandardControlCurrent.PolynomialBoolean.Definitions

@[expose] public section
namespace LogicLineages.StandardControlCurrent.GraphNetwork
open OrdinalComparison PolynomialGraphCompletion WordLinearDecisionCompletion

abbrev HeadClause := Nat × Nat × Nat
abbrev Block := Nat × Expr × Nat
def Block.start (b : Block) := b.1
def Block.term (b : Block) := b.2.1
def Block.result (b : Block) := b.2.2
/-- The designated output wire is linked explicitly; auxiliary nodes are not
silently identified with it. -/
def Block.rows (b : Block) : List Row :=
  rows b.start b.term ++ [variableRow b.result (output b.start b.term)]
def heads (hs : List HeadClause) (bs : List Block) : List Nat :=
  hs.map Prod.fst ++ bs.flatMap (fun b => b.term.heads)
def degree (hs : List HeadClause) (bs : List Block) : Nat := familyDegree (heads hs bs)
def allRows (hs : List HeadClause) (bs : List Block) (rs : List Row) : List Row :=
  hs.map (fun h => headEquation h.1 h.2.1 h.2.2) ++ bs.flatMap Block.rows ++ rs

def LinearRow (r : Row) : Prop := ∀ a ∈ r.2, a.2.2 = []
def LinearFormula (p : Formula) : Prop := ∀ a ∈ p.tokens, a.2 = []
noncomputable def Valid (hs : List HeadClause) (bs : List Block) (rs : List Row) (p : Formula) : Prop :=
  (∀ h ∈ hs, ValidHead h.1) ∧ (∀ b ∈ bs, ValidExpr b.term) ∧
  (∀ r ∈ rs, LinearRow r) ∧ LinearFormula p

/-- Source interface is the already flattened common-valuation graph matrix.
Blocks may collide/cycle as constraints; no independent realization is asserted. -/
noncomputable def SourceHolds (d : Nat) (hs : List HeadClause) (bs : List Block)
    (rs : List Row) (p : Formula) (ν : Nat → Nat) : Prop :=
  PolynomialBoolean.Positive d ν ∧
  (∀ h ∈ hs, ν h.2.2 = headValue h.1 (ν h.2.1)) ∧
  (∀ b ∈ bs, RowsHold b.rows ν) ∧
  (∀ r ∈ rs, RowValue r ν = 0) ∧ Formula.eval ν p

def matrix (d : Nat) (hs : List HeadClause) (bs : List Block) (rs : List Row) (p : Formula) : Formula :=
  .conj (PolynomialBoolean.positiveFormula d)
    (.conj (PolynomialBoolean.graphFormula (allRows hs bs rs)) p)

/-- Simultaneous allocator for valid high-level graph-clause inputs. -/
def allocate (start : Nat) : List (Expr × Nat) → List Block
  | [] => []
  | (t,result)::rest => (start,t,result) :: allocate (start+nodeCount t) rest

def InputBound (n : Nat) (xs : List (Expr × Nat)) : Prop :=
  ∀ x ∈ xs, x.2 < n ∧ ∀ i ∈ x.1.variables, i < n

def AllocationGood (n : Nat) (bs : List Block) : Prop :=
  (∀ b ∈ bs, n ≤ b.start ∧ Fresh b.start b.term ∧ b.result < b.start) ∧
  bs.Pairwise (fun b c => b.start + nodeCount b.term ≤ c.start)

abbrev BlockCode := Nat × Nat × Nat
def encodeBlock (b : Block) : BlockCode := (b.start,b.term.encode,b.result)
abbrev QueryData := List HeadClause × List BlockCode × List Row × Nat
def sourceCode (hs : List HeadClause) (bs : List Block) (rs : List Row) (p : Formula) : Nat :=
  Encodable.encode ((hs,bs.map encodeBlock,rs,p.encode) : QueryData)

namespace Code
/-- Actual expression row machine, with explicit designated-output link. -/
def blockRows (b : BlockCode) : List Row :=
  let a := ExpressionCode.run (ExpressionCode.instructions b.2.1) (b.1,[],[])
  a.2.2 ++ [variableRow b.2.2 (a.2.1.headD 0)]
def blockHeads (b : BlockCode) : List Nat :=
  ExpressionCode.headNames (ExpressionCode.instructions b.2.1)
def decode (n : Nat) : QueryData := (Encodable.decode n).getD ([],[],[],0)
def package (d code : Nat) : Nat × Nat :=
  let q := decode code
  let D := familyDegree (q.1.map Prod.fst ++ q.2.1.flatMap blockHeads)
  let rs := q.1.map (fun h => headEquation h.1 h.2.1 h.2.2) ++
    q.2.1.flatMap blockRows ++ q.2.2.1
  (D,PolynomialBoolean.Code.conj (PolynomialBoolean.Code.positive d)
    (PolynomialBoolean.Code.conj (PolynomialBoolean.Code.graph rs) q.2.2.2))
noncomputable def decide (d code : Nat) : Bool :=
  let p := package d code
  ClosedWordDecisionCompletion.Machine.solve p.1 p.2

def allocate (start : Nat) : List (Nat × Nat) → List BlockCode
  | [] => []
  | (code,result)::rest => (start,code,result) ::
      allocate (start+(ExpressionCode.instructions code).length) rest
end Code
end LogicLineages.StandardControlCurrent.GraphNetwork
