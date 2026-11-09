module
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.RunnerDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.OutcomeTransport
open PolynomialGraphCompletion WordLinearDecisionCompletion
open LayeredComparison.SnyatkovCompletion

/-- Original nonnegative row occurrences, in the literal Boolean atom order.
Repeated rows and every zero coefficient are retained. -/
def inequalityRows (p : Formula) : List Row :=
  p.atoms.filterMap (fun a => match a with
    | .nonnegative r => some r
    | .divisible _ _ => none)

def congruences (p : Formula) : List (Nat × Row) :=
  p.atoms.filterMap (fun a => match a with
    | .nonnegative _ => none
    | .divisible m r => some (m,r))

def CongruencesLinear (maximum : Nat) (p : Formula) : Prop :=
  ∀ a ∈ congruences p, LinearRow maximum a.2

abbrev OutcomeData := Nat × Row
abbrev Table := List (Nat × OutcomeData)

def outcomeData (o : Outcome) : OutcomeData := (o.tag,o.row)

/-- Keys are literal encoded source rows. This table is built by the
original occurrence-order zip; a repeated row uses its first matching
outcome, all of whose correctness facts hold at the same valuation. -/
def makeTable (rows : List Row) (outcomes : List OutcomeData) : Table :=
  (rows.zip outcomes).map (fun p => (Encodable.encode p.1,p.2))

def lookup (key : Nat) : Table → OutcomeData
  | [] => (0,(0,[]))
  | (k,o)::rest => if k = key then o else lookup key rest

def outcomeFormula (o : OutcomeData) : Formula :=
  if o.1 = 0 then .bot else if o.1 = 2 then .top else .atom (.nonnegative o.2)

/-- Only nonnegative atoms consume row outcomes. Every original congruence
and every Boolean constructor is retained literally. -/
def rewriteWith (table : Table) : Formula → Formula
  | .bot => .bot
  | .top => .top
  | .atom (.nonnegative r) => outcomeFormula (lookup (Encodable.encode r) table)
  | .atom (.divisible m r) => .atom (.divisible m r)
  | .neg p => .neg (rewriteWith table p)
  | .conj p q => .conj (rewriteWith table p) (rewriteWith table q)
  | .disj p q => .disj (rewriteWith table p) (rewriteWith table q)

def rewrite (p : Formula) (outcomes : List Outcome) : Formula :=
  rewriteWith (makeTable (inequalityRows p) (outcomes.map outcomeData)) p

structure Matrix where
  tail : Nat
  cases : List Formula

def originalTail (p : Formula) : Nat :=
  Algorithm.foldMax (p.atoms.map (fun a => Algorithm.rowTail a.row))

/-- The old global domain payment remains even when a strict-sign atom is
replaced by a Boolean constant or lies in an unused disjunct. -/
def transform (p : Formula) (pack : Package) : Matrix :=
  ⟨max pack.tail (originalTail p),
    pack.cases.map (fun c => .conj c.guard (rewrite p c.outcomes))⟩

noncomputable def compile (D maximum : Nat) (p : Formula) : Matrix :=
  transform p (Runner.compile D maximum (inequalityRows p))

def encodeMatrix (matrix : Matrix) : Nat × List Nat :=
  (matrix.tail,matrix.cases.map Formula.encode)

noncomputable def MatrixCorrect (D maximum : Nat) (p : Formula) (matrix : Matrix) : Prop :=
  (∀ q ∈ matrix.cases, Formula.allowed D q ∧ linear maximum q = true ∧
    FormulaNamesFrom p.variables q) ∧
  ∀ ν, Region matrix.tail maximum p.variables ν →
    Formula.meaningful p ν ∧
    (∀ q ∈ matrix.cases, Formula.meaningful q ν) ∧
    (Formula.eval ν p ↔ ∃ q ∈ matrix.cases, Formula.eval ν q)

namespace Code

def inequalityRows (code : Nat) : List Row :=
  (LinearRows.Code.atoms code).filterMap (fun payload =>
    let a := WordLinearDecisionCompletion.Code.decodeAtom payload
    if a.1 = 0 then some a.2.2 else none)

def originalTail (code : Nat) : Nat :=
  Algorithm.foldMax ((LinearRows.Code.atoms code).map (fun payload =>
    Algorithm.rowTail (WordLinearDecisionCompletion.Code.decodeAtom payload).2.2))

def outcomeFormula (o : OutcomeData) : Nat :=
  if o.1 = 0 then 1 else if o.1 = 2 then 0
  else 6*Encodable.encode ((0,0,o.2) : WordLinearDecisionCompletion.Code.AtomData)+2

def atom (table : Table) (payload : Nat) : Nat :=
  let a := WordLinearDecisionCompletion.Code.decodeAtom payload
  if a.1 = 0 then outcomeFormula (lookup (Encodable.encode a.2.2) table)
  else 6*payload+2

/-- Literal Boolean substitution on radix-six source codes. The atom
operation returns a complete formula code, so strict signs become constants. -/
def bind (op : Nat → Nat) (code : Nat) : Nat :=
  if code % 6 = 0 then 0 else if code % 6 = 1 then 1
  else if code % 6 = 2 then op (code/6)
  else if code % 6 = 3 then 6*bind op (code/6)+3
  else 6*Nat.pair (bind op (code/6).unpair.1) (bind op (code/6).unpair.2)+code%6
termination_by code
decreasing_by
  all_goals
    have hpos : 0 < code := by omega
    have hd : code/6 < code := Nat.div_lt_self hpos (by decide)
    have hl := Nat.unpair_left_le (code/6)
    have hr := Nat.unpair_right_le (code/6)
    omega

def rewrite (code : Nat) (outcomes : List OutcomeData) : Nat :=
  bind (atom (makeTable (inequalityRows code) outcomes)) code

def transform (code : Nat) (pack : EncodedPackage) : Nat × List Nat :=
  (max pack.1 (originalTail code),
    pack.2.map (fun c => 6*Nat.pair c.1 (rewrite code c.2)+4))

/-- No row solver is an input. This code binds the same concrete actual
Runner.compile used by the frozen whole-row target. -/
noncomputable def compile (D maximum code : Nat) : Nat × List Nat :=
  transform code (encodePackage (Runner.compile D maximum (inequalityRows code)))

end Code
end LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.OutcomeTransport
