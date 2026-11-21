module
public import LogicLineages.PermittedControl.ClosedOrdinaryFieldTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsCodeDefinitions

@[expose] public section
namespace LogicLineages.PermittedControl.PreparedProjection
open OrdinalComparison
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open FieldComparison

/-- Name zero is the natural coordinate eliminated by the kernel. Every
positive name is the original table position plus one. The raw packet
retains the byte code of the table, including unused or repeated slots. -/
abbrev PreparedPacketCode := Nat × Nat

def eliminatePreparedCode (p : PreparedPacketCode) : PreparedPacketCode :=
  (p.1,LinearRows.Code.eliminate 0 p.2)

def eliminatePreparedFormula (p : NormalForm.Formula) : NormalForm.Formula :=
  LinearRows.eliminate 0 p

inductive LowerOperand where
  | coordinate (rank : Nat)
  | ordinary (rank : Nat) (field : ValueField)
  | count (rank : Nat) (lam mu : NONote)

def LowerOperand.rank : LowerOperand → Nat
  | .coordinate rank | .ordinary rank _ | .count rank _ _ => rank

/-- Literal table encoding. Tags distinguish raw coordinate, ordinary
field, and count. Original rank and endpoint/iterate bytes are retained. -/
abbrev LowerOperandCode := Nat × Nat × LongFieldCode

def LowerOperand.code : LowerOperand → LowerOperandCode
  | .coordinate rank => (0,rank,(0,0,0,0))
  | .ordinary rank field => (1,rank,longFieldCode field)
  | .count rank lam mu => (2,rank,longFieldCode (.entry 0 lam mu))

def preparedTableBytes (table : List LowerOperand) : Nat :=
  Encodable.encode (table.map LowerOperand.code)

def preparedPacketCode (table : List LowerOperand) (p : NormalForm.Formula) : PreparedPacketCode :=
  (preparedTableBytes table,p.encode)

/-- Every literal row occurrence, including one with coefficient zero,
has the plain-variable constructor. A positive name must address the
unchanged table; name zero is reserved for the quantified natural. -/
def PlainPreparedFormula (p : NormalForm.Formula) : Prop :=
  ∀ a ∈ LinearRows.atoms p, ∀ s ∈ a.row.2, ∃ i : Nat, s.2 = .variable i

def PreparedInput (table : List LowerOperand) (p : NormalForm.Formula) : Prop :=
  PlainPreparedFormula p ∧ ∀ i ∈ p.variables, i ≤ table.length

def PreparedProjectionCodeExact : Prop :=
  Primrec eliminatePreparedCode ∧
  (∀ p : PreparedPacketCode, (eliminatePreparedCode p).1 = p.1) ∧
  (∀ (bytes : Nat) (p : NormalForm.Formula),
    eliminatePreparedCode (bytes,p.encode) = (bytes,(eliminatePreparedFormula p).encode)) ∧
  ∀ (table : List LowerOperand) (p : NormalForm.Formula),
    eliminatePreparedCode (preparedPacketCode table p) =
      preparedPacketCode table (eliminatePreparedFormula p)

def PreparedProjectionSyntax : Prop :=
  ∀ (table : List LowerOperand) (p : NormalForm.Formula), PreparedInput table p →
    LinearRows.isLinear 0 p = true ∧
    PlainPreparedFormula (eliminatePreparedFormula p) ∧
    (∀ i : Nat, i ∈ (eliminatePreparedFormula p).variables ↔ i ≠ 0 ∧ i ∈ p.variables) ∧
    ∀ i ∈ (eliminatePreparedFormula p).variables, 0 < i ∧ i ≤ table.length

/-- First prove equivalence for arbitrary natural slot assignments.
No assumed realizability and no independent existential on slot values. -/
def PreparedProjectionActual : Prop :=
  ∀ (table : List LowerOperand) (p : NormalForm.Formula), PreparedInput table p →
  ∀ ν : Nat → Nat, (eliminatePreparedFormula p).eval ν ↔
    ∃ z : Nat, p.eval (Function.update ν 0 z)

noncomputable def lowerOperandRead (f : Nat → Nat) (ρ : Nat → Nat) (op : LowerOperand) :
    ClosedNaturalFieldResult :=
  match op with
  | .coordinate rank => some (some (ρ rank))
  | .ordinary rank field => closedOrdinaryValueField f (longFieldCode field) (ρ rank)
  | .count rank lam mu =>
      closedOrdinaryCountField f (rawNoteEncode lam.1,rawNoteEncode mu.1,ρ rank)

def LowerOperandActual (f : Nat → Nat) (ρ : Nat → Nat) (op : LowerOperand) (v : Nat) : Prop :=
  match op with
  | .coordinate rank => v = ρ rank
  | .ordinary rank field =>
      ClosedOrdinaryValueDomain field (ρ rank) ∧ FieldValue f field (ρ rank) v
  | .count rank lam mu =>
      ClosedOrdinaryValueDomain (.entry 0 lam mu) (ρ rank) ∧
        FirstEntry f (countInitial lam.1.repr (ρ rank)) mu.1.repr v

/-- All slots read from one actual raw valuation. Ranks strictly below
the eliminated rank may repeat; repeated occurrences never receive
independent assignments. Every supplied lower value must really exist. -/
def PreparedTableTied (f : Nat → Nat) (zRank : Nat) (ρ : Nat → Nat)
    (table : List LowerOperand) (ν : Nat → Nat) : Prop :=
  ∀ (j : Nat) (hj : j < table.length),
    let op := table.get ⟨j,hj⟩
    op.rank < zRank ∧ LowerOperandActual f ρ op (ν (j+1))

def PreparedTiedProjection : Prop :=
  (∀ (f : Nat → Nat) (ρ : Nat → Nat) (op : LowerOperand) (v : Nat),
    lowerOperandRead f ρ op = some (some v) ↔ LowerOperandActual f ρ op v) ∧
  ∀ (f : Nat → Nat) (zRank : Nat) (ρ : Nat → Nat) (table : List LowerOperand)
      (p : NormalForm.Formula) (ν : Nat → Nat),
    PreparedInput table p → PreparedTableTied f zRank ρ table ν →
    (∀ z : Nat, PreparedTableTied f zRank (Function.update ρ zRank z) table (Function.update ν 0 z)) ∧
    ((eliminatePreparedFormula p).eval ν ↔
      ∃ z : Nat, PreparedTableTied f zRank (Function.update ρ zRank z) table (Function.update ν 0 z) ∧
        p.eval (Function.update ν 0 z))

/-- Prepared one-variable row projection only, not the preparation,
finite strips, or any whole arithmetic/QE theorem. -/
def FullPreparedParameterProjection : Prop :=
  PreparedProjectionCodeExact ∧ PreparedProjectionSyntax ∧
    PreparedProjectionActual ∧ PreparedTiedProjection

end LogicLineages.PermittedControl.PreparedProjection
