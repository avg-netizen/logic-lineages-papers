module
public import LogicLineages.PermittedControl.ActualBitFamilyRawLayoutTargets
public import LogicLineages.PermittedControl.ActualPaidOrderedSyntaxReadsTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualBitFamilyRawReadCeiling
open OrdinalComparison
open PreparedProjection (LowerOperand LowerOperandCode)
open MixedSameRankResidue (WeightedOperand WeightedCode properOperand encodeWeighted)
open ActualPaidOrderedSyntaxReads (operandMinimum readCeiling)
open HeterogeneousSignedMatrixSlice (RawRow Row encodeRow)
open OriginalPrintedTerminalBitClauses (BitRow)
open ActualGuardedResidualBitFamily (Family)
open ActualBitFamilyRawLayout (RawBitRow RawFamily encodeFamily)
open ActualBitFamilyLowSlices (coordinates)
open ActualReadChargeIteration (ReadState)
open ActualZeroClassReplacement (liftedReads)
open ActualBoundedSignedRouteSemantics (stateSyntax)

def operandCode (op : LowerOperandCode) : Nat :=
  let field := op.2.2
  if op.1 = 0 ∨ field.1 = 0 then 0
  else max 2 (max (rawNormCode field.2.2.1) (rawNormCode field.2.2.2))

def termsCode (terms : List WeightedCode) : Nat :=
  terms.foldr (fun t n => max (operandCode t.2) n) 0

def rowCode (r : RawRow) : Nat := termsCode r.2.2

def clauseCode (rs : List RawBitRow) : Nat :=
  rs.foldr (fun r n => max (rowCode r.1) n) 0

def familyCode (family : RawFamily) : Nat :=
  family.foldr (fun rs n => max (clauseCode rs) n) 0

noncomputable def familyCeiling (family : Family) : Nat :=
  family.foldr (fun rs n =>
    max (rs.foldr (fun r acc => max (readCeiling r.1.2.2) acc) 0) n) 0

def ExactReadCeilingCalibration : Prop :=
  (∀ op : LowerOperand, operandCode op.code = operandMinimum op) ∧
  (∀ terms : List WeightedOperand, termsCode (terms.map encodeWeighted) = readCeiling terms) ∧
  (∀ r : Row, rowCode (encodeRow r) = readCeiling r.2.2) ∧
  ∀ family : Family, familyCode (encodeFamily family) = familyCeiling family

/-- An encoded bound offers actual original read evidence only when
its rank hypothesis is paid by one real valuation and the operands
are proper. The bound does not test properness itself. -/
def ExactRawReadFunding : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
    ∀ (ρ : Nat → Nat) (family : Family),
      (∀ k ∈ coordinates family, familyCode (encodeFamily family) ≤ ρ k) →
      ∀ clause ∈ family, ∀ r ∈ clause,
        (∀ t ∈ r.1.2.2, properOperand t.2) →
        ∃ measured : ReadState,
          stateSyntax measured = ⟨r.1.2.1,r.1.2.2⟩ ∧ liftedReads f ρ measured.reads

def ExactRawReadCeilingEffectivity : Prop :=
  Primrec operandCode ∧ Primrec termsCode ∧ Primrec rowCode ∧ Primrec clauseCode ∧ Primrec familyCode

def FullActualBitFamilyRawReadCeiling : Prop :=
  ExactReadCeilingCalibration ∧ ExactRawReadFunding ∧ ExactRawReadCeilingEffectivity

end LogicLineages.PermittedControl.ActualBitFamilyRawReadCeiling
