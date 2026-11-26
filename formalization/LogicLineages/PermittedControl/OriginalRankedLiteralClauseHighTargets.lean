module
public import LogicLineages.PermittedControl.OriginalPrintedLiteralRowBridgeTargets
public import LogicLineages.PermittedControl.ActualSelectedSignedRouteProjectionTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalRankedLiteralClauseHigh
open OrdinalComparison PreparedProjection
open ActualPreparedSlotAppend (Packet)
open ActualSelectedSignedRouteProjection (project LowerHolds)
open ActualBoundedSignedRoutes (PacketHolds)
open ActualRankedNormalizationSyntax (LowerStrict)
open ActualTraceSignCutoff (terminalCutoffCeiling)
open ActualPaidOrderedSyntaxReads (PaidReadCeiling readCeiling)
open ActualPaidSignedRouteReplay (commonMinimum dummy)
open ActualGreatestCongruenceRoute (modulusMinimum)
open ActualPaidMixedMatrixTuples (MixedRow Ready matrixMinimum tuples)
open ActualSignedRouteCartesian (tuplePacket)
open OriginalPrintedTerminalBitClauses (BitRow ClauseHolds)
open OriginalPrintedLiteralRowBridge (properClauses compileRow)

noncomputable def staticNeed (B r : Nat) : MixedRow → Nat
  | .signed row => max (commonMinimum B r row.source) (terminalCutoffCeiling r (dummy row.source))
  | .modular m s _ => modulusMinimum B m s

noncomputable def rowNeed (B r : Nat) (row : BitRow) : Nat :=
  max (readCeiling row.1.2.2) (staticNeed B r (compileRow row))

noncomputable def clauseNeed (B r : Nat) (rows : List BitRow) : Nat :=
  rows.foldr (fun row tail => max (rowNeed B r row) tail) 0

noncomputable def familyNeed (B r : Nat) (family : List (List BitRow)) : Nat :=
  (properClauses family).foldr (fun rows tail => max (clauseNeed B r rows) tail) 0

def rankedPredecessor (top : Nat) (baseline : Nat → Nat) : Nat :=
  if top = 0 then 0 else baseline (top-1)+1

/-- The family threshold itself is independent of the valuation.
Strict rank replay adds only the previous actual raw rank plus one. -/
noncomputable def highMinimum (B r top : Nat) (baseline : Nat → Nat) (family : List (List BitRow)) : Nat :=
  max (familyNeed B r family) (rankedPredecessor top baseline)

structure OriginalSetup (B r top : Nat) (baseline : Nat → Nat) (family : List (List BitRow)) : Prop where
  strict : LowerStrict baseline top
  scope : ∀ rows ∈ family, ∀ row ∈ rows, ∀ t ∈ row.1.2.2, t.2.rank < r ∧ t.2.rank ≤ top
  lower : ∀ rows ∈ properClauses family, ∀ row ∈ rows, ∀ t ∈ row.1.2.2, t.2.rank < top →
    familyNeed B r family ≤ baseline t.2.rank

noncomputable def highPackets (r top : Nat) (family : List (List BitRow)) : List Packet :=
  (properClauses family).flatMap (fun rows => (tuples r top (rows.map compileRow)).map tuplePacket)

def SourceFamily (f ρ : Nat → Nat) (family : List (List BitRow)) : Prop :=
  ∃ rows ∈ family, ClauseHolds f ρ rows

def ExactOriginalLiteralReady : Prop :=
  ∀ (B r top : Nat) (baseline : Nat → Nat) (family : List (List BitRow)),
    OriginalSetup B r top baseline family →
    ∀ (z : Nat), highMinimum B r top baseline family ≤ z →
    ∀ rows ∈ properClauses family,
      (∀ row ∈ rows, PaidReadCeiling (Function.update baseline top z) row.1.2.2) ∧
      (∀ row ∈ rows.map compileRow, Ready B r top baseline row) ∧
      matrixMinimum B r top baseline (rows.map compileRow) ≤ z

def ExactRankedLiteralHigh : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
    ∀ (r top : Nat) (baseline : Nat → Nat) (family : List (List BitRow)),
      OriginalSetup B r top baseline family →
      ∀ (z : Nat), highMinimum B r top baseline family ≤ z →
        (SourceFamily f (Function.update baseline top z) family ↔
          ∃ q ∈ highPackets r top family, PacketHolds f baseline top z q)

def ExactRankedLiteralHighProjection : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
    ∀ (r top : Nat) (baseline : Nat → Nat) (family : List (List BitRow)),
      OriginalSetup B r top baseline family →
      ∀ prior : (Nat → Nat) → Prop,
        let minimum := highMinimum B r top baseline family
        (∀ z : Nat, minimum ≤ z → (prior (Function.update baseline top z) ↔ prior baseline)) →
        ((prior baseline ∧ ∃ q ∈ highPackets r top family,
            LowerHolds f baseline top (project minimum q)) ↔
          ∃ z : Nat, minimum ≤ z ∧ prior (Function.update baseline top z) ∧
            SourceFamily f (Function.update baseline top z) family)

def FullOriginalRankedLiteralClauseHigh : Prop :=
  ExactOriginalLiteralReady ∧ ExactRankedLiteralHigh ∧ ExactRankedLiteralHighProjection

end LogicLineages.PermittedControl.OriginalRankedLiteralClauseHigh
