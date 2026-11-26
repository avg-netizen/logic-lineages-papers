module
public import LogicLineages.PermittedControl.OriginalPrintedLiteralRowBridgeTargets
public import LogicLineages.PermittedControl.ActualBitFamilyRawClosedTargets
public import LogicLineages.OrdinalComparison.RawComparisonDefinitions
public import LogicLineages.OrdinalComparison.OrdinalSuccessorProgramDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.PermittedControl.RawProperClause
open OrdinalComparison (rawNoteEncode rawComparisonCode encodedOrdinalFiniteRemainder)
open PreparedProjection (LowerOperand LowerOperandCode)
open FieldComparison (ValueField ProperField LongFieldCode longFieldCode)
open MixedSameRankResidue (WeightedCode properOperand)
open SignedRowGuardedTest (Test)
open HeterogeneousSignedMatrixSlice (encodeTest)
open OriginalPrintedTerminalBitClauses (BitRow)
open OriginalPrintedLiteralRowBridge (properClauses AdmittedOperandRow AdmittedLiteralClause)
open ActualGuardedResidualBitFamily (Family)
open ActualBitFamilyRawLayout (RawBitRow RawFamily encodeBitRow encodeFamily)
open ActualBitFamilyRawClosed (admittedCode)

/-- Successor-limit test on the existing raw notation code: nonzero code and
zero finite remainder of the existing raw split program. -/
def limitCode (n : Nat) : Bool :=
  decide (0 < n) && decide (encodedOrdinalFiniteRemainder n = 0)

/-- Proper-interval test on the existing four-component field code
(tag, exponent, upper endpoint code, lower endpoint code). Tag zero is an
iterate; every nonzero tag is read as an entry, as `longFieldCode` documents. -/
def properFieldCode (c : LongFieldCode) : Bool :=
  if c.1 = 0 then true
  else (limitCode c.2.2.1 && (decide (c.2.2.2 = 0) || limitCode c.2.2.2)) &&
    decide (rawComparisonCode c.2.2.2 c.2.2.1 = 0)

/-- Operand test on the existing operand code (tag, rank, field code).
Tag zero is a raw coordinate; ordinary and count tags test their field code. -/
def properOperandCode (op : LowerOperandCode) : Bool :=
  if op.1 = 0 then true else properFieldCode op.2.2

def admittedRowCode (r : RawBitRow) : Bool :=
  admittedCode r.1.1 && r.1.2.2.all (fun t : WeightedCode => properOperandCode t.2)

def admittedClauseCode (rows : List RawBitRow) : Bool := rows.all admittedRowCode

/-- The raw proper-clause filter on encoded families. -/
def properClausesCode (family : RawFamily) : RawFamily := family.filter admittedClauseCode

def ExactLimitCode : Prop :=
  ∀ eta : NONote, limitCode (rawNoteEncode eta.1) = true ↔ Order.IsSuccLimit eta.1.repr

def ExactProperFieldCode : Prop :=
  ∀ F : ValueField, properFieldCode (longFieldCode F) = true ↔ ProperField F

def ExactProperOperandCode : Prop :=
  ∀ op : LowerOperand, properOperandCode op.code = true ↔ properOperand op

def ExactAdmittedTestCode : Prop :=
  ∀ t : Test, admittedCode (encodeTest t) = true ↔ t.Admitted

def ExactAdmittedRowCode : Prop :=
  ∀ row : BitRow, admittedRowCode (encodeBitRow row) = true ↔ AdmittedOperandRow row

def ExactAdmittedClauseCode : Prop :=
  ∀ rows : List BitRow,
    admittedClauseCode (rows.map encodeBitRow) = true ↔ AdmittedLiteralClause rows

/-- Literal list equation: the raw filter on the encoded family is the
encoding of the typed classical filter, in the same order. -/
def ExactRawProperClauses : Prop :=
  ∀ family : Family, properClausesCode (encodeFamily family) = encodeFamily (properClauses family)

/-- The operand code determines the operand (in particular the notations). -/
def ExactOperandCodeInjective : Prop :=
  ∀ op op' : LowerOperand, op.code = op'.code → op = op'

def ExactRawProperClauseEffectivity : Prop :=
  Primrec limitCode ∧ Primrec properFieldCode ∧ Primrec properOperandCode ∧
    Primrec admittedRowCode ∧ Primrec admittedClauseCode ∧ Primrec properClausesCode ∧
    Computable properClausesCode

def FullRawProperClause : Prop :=
  ExactLimitCode ∧ ExactProperFieldCode ∧ ExactProperOperandCode ∧ ExactAdmittedTestCode ∧
    ExactAdmittedRowCode ∧ ExactAdmittedClauseCode ∧ ExactRawProperClauses ∧
    ExactOperandCodeInjective ∧ ExactRawProperClauseEffectivity

end LogicLineages.PermittedControl.RawProperClause
