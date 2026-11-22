module
public import LogicLineages.PermittedControl.ActualBitFamilyRawLayoutTargets
public import LogicLineages.PermittedControl.ActualBitFamilyExistentialLowTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualBitFamilyRawClosed
open ActualBitFamilyRawLayout (RawBitRow RawFamily encodeBitRow encodeFamily)
open HeterogeneousSignedMatrixSlice (TestCode)
open OriginalPrintedTerminalBitClauses (BitRow)
open ActualGuardedResidualBitFamily (Family)
open ActualBitFamilyExistentialLow (closedClause closed Satisfiable)
open ActualBitFamilyLowSlices (dimension)

/-- The natural payload of the three scalar tags must be zero. For the
congruence tag it must be positive, independently of the wanted bit. -/
def admittedCode (test : TestCode) : Bool :=
  (decide (test.1 < 3) && decide (test.2 = 0)) ||
    (decide (test.1 = 3) && decide (0 < test.2))

def testCode (p : TestCode × Int) : Bool :=
  if p.1.1 = 0 then decide (p.2 = 0)
  else if p.1.1 = 1 then decide (p.2.sign = 0) || decide (p.2.sign = 1)
  else if p.1.1 = 2 then decide (p.2.sign = 1)
  else decide (p.2.natAbs % p.1.2 = 0)

/-- An unadmitted test or a still-open row cannot become a false result
matching a false wanted bit. Both reject the whole clause. -/
def rowCode (r : RawBitRow) : Bool :=
  admittedCode r.1.1 && (decide (r.1.2.2.length = 0) &&
    decide (testCode (r.1.1,r.1.2.1) = r.2))

def clauseCode (rows : List RawBitRow) : Bool := rows.all rowCode

def closedCode (family : RawFamily) : Bool := family.any clauseCode

def ExactClosedRawCalibration : Prop :=
  (∀ clause : List BitRow, clauseCode (clause.map encodeBitRow) = closedClause clause) ∧
  ∀ family : Family, closedCode (encodeFamily family) = closed family

def ExactClosedRawTruth : Prop :=
  ∀ (f : Nat → Nat) (family : Family), dimension family = 0 →
    (closedCode (encodeFamily family) = true ↔ Satisfiable f family)

def ExactClosedRawEffectivity : Prop :=
  Primrec admittedCode ∧ Primrec testCode ∧ Primrec rowCode ∧
    Primrec clauseCode ∧ Primrec closedCode

def FullActualBitFamilyRawClosed : Prop :=
  ExactClosedRawCalibration ∧ ExactClosedRawTruth ∧ ExactClosedRawEffectivity

end LogicLineages.PermittedControl.ActualBitFamilyRawClosed
