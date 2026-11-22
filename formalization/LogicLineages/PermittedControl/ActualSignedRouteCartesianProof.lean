module
public import LogicLineages.PermittedControl.ActualSignedRouteCartesianTargets
import LogicLineages.PermittedControl.ActualSignedRouteCartesianChoiceProof
import LogicLineages.PermittedControl.ActualSelectedSignedRoutePacketProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualSignedRouteCartesian
open ActualPreparedSlotAppend (Packet)
open ActualSelectedSignedRoutePacket (packet Shape exactEmittedRouteFamily)
open ActualBoundedSignedRoutes (PacketHolds)
open ActualSyntaxChargeBudget (syntaxBudget)

theorem exactActualSignedMatrixTuples : ExactActualSignedMatrixTuples := by
  intro f baseline r top z rows
  have rowExact (row : SignedRow) := exactEmittedRouteFamily f baseline top z
    (syntaxBudget r row.source.terms) row.test row.positive row.source
  have shape (ps : List Packet) (fromRows : ps ∈ rows.map (rowPackets r top)) :
      ∀ p ∈ ps, Shape p := by
    obtain ⟨row,_,rfl⟩ := List.mem_map.mp fromRows
    intro p used
    obtain ⟨path,member,rfl⟩ := List.mem_map.mp used
    exact (rowExact row).1 path member
  have rowEval (row : SignedRow) :
      (∃ p ∈ rowPackets r top row, PacketHolds f baseline top z p) ↔ RowHolds f baseline r top z row := by
    refine Iff.trans ?_ (rowExact row).2
    constructor
    · rintro ⟨p,used,passes⟩
      obtain ⟨path,member,rfl⟩ := List.mem_map.mp used
      exact ⟨path,member,passes⟩
    · rintro ⟨path,used,passes⟩
      exact ⟨packet row.test row.positive path,List.mem_map.mpr ⟨path,used,rfl⟩,passes⟩
  have result := exactCartesianPacketEval f baseline top z (rows.map (rowPackets r top)) shape
  refine ⟨result.1,result.2.trans ?_⟩
  constructor
  · intro h row used
    exact (rowEval row).mp (h (rowPackets r top row) (List.mem_map.mpr ⟨row,used,rfl⟩))
  · intro h ps used
    obtain ⟨row,member,rfl⟩ := List.mem_map.mp used
    exact (rowEval row).mpr (h row member)

end LogicLineages.PermittedControl.ActualSignedRouteCartesian
