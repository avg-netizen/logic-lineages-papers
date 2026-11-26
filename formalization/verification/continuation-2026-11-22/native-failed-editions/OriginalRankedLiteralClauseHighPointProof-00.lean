module
public import LogicLineages.PermittedControl.OriginalRankedLiteralClauseHighTargets
import LogicLineages.PermittedControl.OriginalRankedLiteralClauseHighReadyProof
import LogicLineages.PermittedControl.ActualPaidMixedMatrixTuplesProof
import LogicLineages.PermittedControl.OriginalPrintedLiteralRowBridgeProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalRankedLiteralClauseHigh
open ActualSelectedSignedRoutePacket (Shape)
open ActualPaidMixedMatrixTuples (tuples exactPaidMixedMatrixTuples exactMixedTupleShape)
open ActualSignedRouteCartesian (tuplePacket)
open OriginalPrintedLiteralRowBridge (compileRow exactLiteralProperClauseFilter exactLiteralMixedClauseBridge properClauseMember)

theorem highPacketShape (r top : Nat) (family : List (List OriginalPrintedTerminalBitClauses.BitRow)) :
    ∀ q ∈ highPackets r top family, Shape q := by
  intro q used
  obtain ⟨rows,_,here⟩ := List.mem_flatMap.mp used
  obtain ⟨tuple,member,rfl⟩ := List.mem_map.mp here
  exact exactMixedTupleShape r top (rows.map compileRow) tuple member

theorem exactRankedLiteralHigh : ExactRankedLiteralHigh := by
  intro f B selected r top baseline family setup z payment
  let θ := Function.update baseline top z
  have original := exactLiteralProperClauseFilter f θ family
  refine original.trans ?_
  constructor
  · rintro ⟨rows,member,live⟩
    have ready := exactOriginalLiteralReady B r top baseline family setup z payment rows member
    have source := (exactLiteralMixedClauseBridge f B selected θ rows
      ((properClauseMember family rows).mp member).2 ready.1).mp live
    obtain ⟨tuple,chosen,actual⟩ :=
      (exactPaidMixedMatrixTuples f B selected r top baseline (rows.map compileRow)
        ready.2.1 z ready.2.2).mp source
    exact ⟨tuplePacket tuple,List.mem_flatMap.mpr ⟨rows,member,List.mem_map.mpr ⟨tuple,chosen,rfl⟩⟩,actual⟩
  · rintro ⟨q,used,actual⟩
    obtain ⟨rows,member,rest⟩ := List.mem_flatMap.mp used
    obtain ⟨tuple,chosen,rfl⟩ := List.mem_map.mp rest
    have ready := exactOriginalLiteralReady B r top baseline family setup z payment rows member
    have source := (exactPaidMixedMatrixTuples f B selected r top baseline (rows.map compileRow)
      ready.2.1 z ready.2.2).mpr ⟨tuple,chosen,actual⟩
    exact ⟨rows,member,(exactLiteralMixedClauseBridge f B selected θ rows
      ((properClauseMember family rows).mp member).2 ready.1).mpr source⟩

end LogicLineages.PermittedControl.OriginalRankedLiteralClauseHigh
