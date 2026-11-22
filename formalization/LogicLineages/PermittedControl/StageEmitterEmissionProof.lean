module
public import LogicLineages.PermittedControl.StageEmitterHighTargets
import LogicLineages.PermittedControl.StageCallbackRawLevelProof
import LogicLineages.PermittedControl.RawPacketAlgebraJoinCalibrationProof
import LogicLineages.PermittedControl.RawPacketAlgebraChildProof
import LogicLineages.PermittedControl.RawProperClauseProof
import LogicLineages.PermittedControl.ActualBitFamilyRawRankProof
import LogicLineages.PermittedControl.ActualRawStageCutoffProof

public section
namespace LogicLineages.PermittedControl.StageEmitter
open StageCallbackRawLevel (Rendering rowCode exactRawRowPackets)
open StageCallbackLevelOrder (levelOrder)
open StageCallbackSupplier (Emits packets child stageChildren compile)
open RawPacketAlgebra (childCode joinCode encodePacket exactJoinCode exactChildCode)
open RawProperClause (properClausesCode exactRawProperClauses)
open ActualBitFamilyRawRank (familyCode exactRawRankCalibration)
open ActualBitFamilyRawLayout (RawFamily encodeBitRow encodeFamily)
open ActualRawStageCutoff (stageBound exactRawStageNamesAndCharts)
open ActualFiniteOrderBranches (Pattern)
open ActualSignedRouteCartesian (choices tuplePacket)
open ActualBitFamilyHigh (ranked)
open OriginalPrintedLiteralRowBridge (properClauses)
open OriginalPrintedTerminalBitClauses (BitRow)
open ActualGuardedResidualBitFamily (Family)
open OriginalPrintedPlainMatrixLinearProjection (top)

/-- One clause: raw rows through the raw row program and the raw join are the
encoded joined packets of the level-order supplier. -/
theorem clauseJoin (R : Rendering) (hR : R.Exact) (r t : Nat) (rows : List BitRow) :
    joinCode ((rows.map encodeBitRow).map (rowCode R r t)) =
      ((choices (rows.map (levelOrder r t))).map tuplePacket).map encodePacket := by
  have pointwise : (rows.map encodeBitRow).map (rowCode R r t) =
      (rows.map (levelOrder r t)).map (List.map encodePacket) := by
    rw [List.map_map,List.map_map]
    exact List.map_congr_left (fun row _ => exactRawRowPackets R hR r t row)
  rw [pointwise]
  exact exactJoinCode (rows.map (levelOrder r t))

/-- All kept clauses, flattened in literal order. -/
theorem clausesJoin (R : Rendering) (hR : R.Exact) (r t : Nat) (family : Family) :
    (encodeFamily family).flatMap (fun rows => joinCode (rows.map (rowCode R r t))) =
      (family.flatMap (fun rows => (choices (rows.map (levelOrder r t))).map tuplePacket)).map
        encodePacket := by
  induction family with
  | nil => rfl
  | cons rows family ih =>
    change joinCode ((rows.map encodeBitRow).map (rowCode R r t)) ++
        (encodeFamily family).flatMap (fun rows => joinCode (rows.map (rowCode R r t))) = _
    rw [ih,clauseJoin R hR r t rows,List.flatMap_cons,List.map_append]

/-- One chart: the raw chart program is the encoding of the typed child. -/
theorem chartCodeEq (R : Rendering) (hR : R.Exact) (C : Nat) (fs : Family) (p : Pattern) :
    chartCode R C (encodeFamily fs) p = encodeFamily (child levelOrder C fs p) := by
  unfold chartCode
  rw [exactRawRankCalibration p fs,exactRawProperClauses (ranked p fs),clausesJoin R hR p.1 (top p)]
  exact exactChildCode C (top p) (packets levelOrder p.1 (top p) (ranked p fs))

theorem exactStageEmission : ExactStageEmission := by
  intro R hR B fs _
  have charts := (exactRawStageNamesAndCharts.2 fs).2
  change (ActualBitFamilyRawCharts.charts (encodeFamily fs)).map
      (chartCode R (stageBound B (encodeFamily fs)) (encodeFamily fs)) =
    (((ActualNamedBitFamilyHigh.charts (ActualBitFamilyRawLayout.names (encodeFamily fs))).map
      (fun p => (p,child levelOrder (stageBound B (encodeFamily fs)) fs p))).map Prod.snd).map encodeFamily
  rw [charts,List.map_map,List.map_map]
  exact List.map_congr_left (fun p _ => chartCodeEq R hR _ fs p)

#print axioms exactStageEmission
end LogicLineages.PermittedControl.StageEmitter
