module
public import LogicLineages.PermittedControl.OriginalMatrixActualHighPacketTargets
public import LogicLineages.PermittedControl.OriginalPrintedPlainMatrixInfiniteLowTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedPlainMatrixSupportLow
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open OriginalPrintedCircuitSequential (Gate)
open OriginalPrintedPlainMatrixOrderBranches (SourceAccepts)
open OriginalPrintedPlainMatrixInfiniteLow (matrix circuit)
open OriginalMatrixActualHighPacket (originalFamilyCeiling)
open OriginalMatrixDenseRanks (support)
open OriginalNormalizedCircuitMatrix (passingList)
open HeterogeneousSignedMatrixSlice (Snapshot actualRows HitRows)
open HeterogeneousSignedMatrixLowStrips (branches)

def LowAt (f : Nat → Nat) (B : Nat) (θ : Nat → Nat) (known : List Nat) (gates : List Gate)
    (p : NormalForm.Formula) (prior : (Nat → Nat) → Prop) (polarity : Bool) (rank : Nat) : Prop :=
  ∃ branch residual,
    branch ∈ branches f rank (originalFamilyCeiling B known gates p) (matrix known gates p) ∧
    branch.1 = θ rank ∧ HitRows branch.2 residual ∧ prior θ ∧
    ∃ suffix : Snapshot,
      actualRows f θ residual (passingList θ (circuit known gates p) ++ suffix) ∧
      OriginalPlainTerminalMatrix.accepts p polarity suffix

/-- The row snapshot at the current shared valuation follows the exact
branch at that valuation's selected digit, not another below-bound value. -/
def ExactOriginalSupportLowAt : Prop :=
  ∀ (f : Nat → Nat) (B : Nat) (θ : Nat → Nat) (known : List Nat) (gates : List Gate)
    (p : NormalForm.Formula), PreparedProjection.PlainPreparedFormula p →
    ∀ (prior : (Nat → Nat) → Prop) (polarity : Bool) (rank : Nat),
      rank ∈ support (matrix known gates p) → θ rank < originalFamilyCeiling B known gates p →
        ((prior θ ∧ SourceAccepts f θ known gates p polarity) ↔
          LowAt f B θ known gates p prior polarity rank)

/-- Every literal name of the actual emitted matrix is eligible, not
only the exterior input list. The *same* normalized graph and protected
exterior are used on the chosen hidden or original name. -/
def ExactOriginalSupportLowStrips : Prop :=
  ∀ (f : Nat → Nat) (B : Nat) (ρ : Nat → Nat) (known : List Nat) (gates : List Gate)
    (p : NormalForm.Formula), PreparedProjection.PlainPreparedFormula p →
    ∀ (prior : (Nat → Nat) → Prop) (polarity : Bool) (rank : Nat),
      rank ∈ support (matrix known gates p) →
        ((∃ a : Nat, a < originalFamilyCeiling B known gates p ∧
          let θ := Function.update ρ rank a
          prior θ ∧ SourceAccepts f θ known gates p polarity) ↔
          ∃ branch residual,
            branch ∈ branches f rank (originalFamilyCeiling B known gates p) (matrix known gates p) ∧
            HitRows branch.2 residual ∧
            let θ := Function.update ρ rank branch.1
            prior θ ∧ ∃ suffix : Snapshot,
              actualRows f θ residual (passingList θ (circuit known gates p) ++ suffix) ∧
              OriginalPlainTerminalMatrix.accepts p polarity suffix)

def FullOriginalPrintedPlainMatrixSupportLow : Prop := ExactOriginalSupportLowAt ∧ ExactOriginalSupportLowStrips

end LogicLineages.PermittedControl.OriginalPrintedPlainMatrixSupportLow
