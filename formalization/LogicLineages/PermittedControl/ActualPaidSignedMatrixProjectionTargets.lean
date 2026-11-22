module
public import LogicLineages.PermittedControl.ActualSignedRouteCartesianTargets
public import LogicLineages.PermittedControl.ActualSelectedSignedRouteProjectionTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualPaidSignedMatrixProjection
open OrdinalComparison
open ActualPaidSignedRouteReplay (LowerSetup SourceHolds replayMinimum)
open ActualSelectedSignedRoutePacket (Shape)
open ActualSignedRouteCartesian (SignedRow tuplePacket matrixTuples)
open ActualSelectedSignedRouteProjection (project LowerHolds)
open ActualBoundedSignedRoutes (PacketHolds)

noncomputable def matrixMinimum (B r top : Nat) (baseline : Nat → Nat) (rows : List SignedRow) : Nat :=
  rows.foldr (fun row n => max (replayMinimum B r top baseline row.source) n) 0

def MatrixSourceHolds (f ρ : Nat → Nat) (rows : List SignedRow) : Prop :=
  ∀ row ∈ rows, SourceHolds f ρ row.source row.test row.positive

def ExactMatrixMinimum : Prop :=
  ∀ (B r top : Nat) (baseline : Nat → Nat) (rows : List SignedRow) (z : Nat),
    matrixMinimum B r top baseline rows ≤ z ↔
      ∀ row ∈ rows, replayMinimum B r top baseline row.source ≤ z

def ExactActualSameHighMatrixTuples : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
    ∀ (r top : Nat) (baseline : Nat → Nat) (rows : List SignedRow),
      (∀ row ∈ rows, LowerSetup B r top baseline row.source) →
      ∀ z : Nat, matrixMinimum B r top baseline rows ≤ z →
        (MatrixSourceHolds f (Function.update baseline top z) rows ↔
         ∃ positions ∈ matrixTuples r top rows,
            PacketHolds f baseline top z (tuplePacket positions))

/-- A finite conjunction, with literal signed test/polarity per row.
A selected tuple is assembled before the single common z is eliminated. -/
def ExactPaidSignedMatrixProjection : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
    ∀ (r top : Nat) (baseline : Nat → Nat) (rows : List SignedRow),
      (∀ row ∈ rows, LowerSetup B r top baseline row.source) →
      ∀ prior : (Nat → Nat) → Prop,
        let minimum := matrixMinimum B r top baseline rows
        (∀ z : Nat, minimum ≤ z → (prior (Function.update baseline top z) ↔ prior baseline)) →
        ((prior baseline ∧ ∃ positions ∈ matrixTuples r top rows,
            LowerHolds f baseline top (project minimum (tuplePacket positions))) ↔
         ∃ z : Nat, minimum ≤ z ∧ prior (Function.update baseline top z) ∧
           MatrixSourceHolds f (Function.update baseline top z) rows)

def FullActualPaidSignedMatrixProjection : Prop :=
  ExactMatrixMinimum ∧ ExactActualSameHighMatrixTuples ∧ ExactPaidSignedMatrixProjection

end LogicLineages.PermittedControl.ActualPaidSignedMatrixProjection
