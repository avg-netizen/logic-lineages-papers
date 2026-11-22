module
public import LogicLineages.PermittedControl.OriginalPrintedTerminalBitClausesTargets
public import LogicLineages.PermittedControl.ActualPaidMixedMatrixTuplesTargets
public import LogicLineages.PermittedControl.ActualInitialSignedCountCleanupTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedLiteralRowBridge
open OrdinalComparison PreparedProjection
open OriginalPrintedTerminalBitClauses (BitRow RowHolds ClauseHolds)
open HeterogeneousSignedMatrixSlice (Row)
open MixedSameRankResidue (WeightedOperand properOperand)
open SignedRowSliceValue (valueAt)
open SignedRowGuardedTest (Test)
open ActualSymbolicZeroSuccessor (SyntaxState)
open ActualSignedOrdinaryPairHigh (OrderTest)
open ActualZeroClassReplacement (liftedReads)
open ActualReadChargeIteration (ReadState stateValue)
open ActualBoundedSignedRouteSemantics (stateSyntax)
open ActualPaidOrderedSyntaxReads (PaidReadCeiling)
open ActualPaidMixedMatrixTuples (MixedRow Source MatrixSource)
open ActualInitialSignedCountCleanup (cleanup)

def originalSyntax (row : Row) : SyntaxState := ⟨row.2.1,row.2.2⟩

def AdmittedOperandRow (r : BitRow) : Prop :=
  r.1.1.Admitted ∧ ∀ t ∈ r.1.2.2, properOperand t.2

def AdmittedLiteralClause (rows : List BitRow) : Prop :=
  ∀ row ∈ rows, AdmittedOperandRow row

/-- A malformed actual original field prevents its whole row from
having a value. Never change its signed bit to false. -/
noncomputable def properClauses (family : List (List BitRow)) : List (List BitRow) :=
  family.filter (fun rows => @decide (AdmittedLiteralClause rows) (Classical.propDecidable _))

def compileRow (row : BitRow) : MixedRow :=
  let s := originalSyntax row.1
  match row.1.1 with
  | .equalZero => .signed ⟨cleanup s,.equalZero,row.2⟩
  | .nonnegative => .signed ⟨cleanup s,.nonnegative,row.2⟩
  | .positive => .signed ⟨cleanup s,.positive,row.2⟩
  | .congruence m => .modular m s row.2

def ExactActualRowReadState : Prop :=
  ∀ (f ρ : Nat → Nat) (c : Int) (ts : List WeightedOperand) (v : Int),
    (valueAt f ρ c ts v ↔ ∃ s : ReadState,
      stateSyntax s = ⟨c,ts⟩ ∧ liftedReads f ρ s.reads ∧ stateValue s = v)

def ExactLiteralRowProper : Prop :=
  ∀ (f ρ : Nat → Nat) (row : BitRow), RowHolds f ρ row → AdmittedOperandRow row

def ExactLiteralProperClauseFilter : Prop :=
  ∀ (f ρ : Nat → Nat) (family : List (List BitRow)),
    (∃ c ∈ family, ClauseHolds f ρ c) ↔
      ∃ c ∈ properClauses family, ClauseHolds f ρ c

/-- Only the signed order rows are cleaned. Their original pre-cleanup
reads remain owed; modular rows are literal and keep the same modulus. -/
def ExactLiteralMixedRowBridge : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
    ∀ (ρ : Nat → Nat) (row : BitRow), AdmittedOperandRow row → PaidReadCeiling ρ row.1.2.2 →
      (RowHolds f ρ row ↔ Source f ρ (compileRow row))

def ExactLiteralMixedClauseBridge : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
    ∀ (ρ : Nat → Nat) (rows : List BitRow), AdmittedLiteralClause rows →
      (∀ row ∈ rows, PaidReadCeiling ρ row.1.2.2) →
      (ClauseHolds f ρ rows ↔ MatrixSource f ρ (rows.map compileRow))

def FullOriginalPrintedLiteralRowBridge : Prop :=
  ExactActualRowReadState ∧ ExactLiteralRowProper ∧ ExactLiteralProperClauseFilter ∧
    ExactLiteralMixedRowBridge ∧ ExactLiteralMixedClauseBridge

end LogicLineages.PermittedControl.OriginalPrintedLiteralRowBridge
