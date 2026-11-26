module
public import LogicLineages.PermittedControl.OriginalPrintedUniformHighResidualTargets
import LogicLineages.PermittedControl.ActualSymbolicPredecessorProjectionProof
import LogicLineages.PermittedControl.OriginalRankedLiteralClauseHighPointProof
import LogicLineages.PermittedControl.ActualSelectedSignedRouteProjectionChosenProof
import LogicLineages.PermittedControl.ActualGreatestRouteResidualProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedUniformHighResidual
open ActualPreparedSlotAppend (Packet)
open ActualSelectedSignedRoutePacket (Shape)
open ActualSelectedSignedRouteProjection (project LowerHolds exactChosenRouteProjection)
open ActualSymbolicPredecessorProjection (prepend exactSymbolicPredecessorAppend exactSymbolicPredecessorProjection)
open ActualGreatestRouteResidual (LowerMatrix exactActualLowerRouteFamily)
open OriginalPrintedRankedLiteralHigh (rankedFamily chartMinimum cutoff)
open OriginalPrintedPlainMatrixLinearProjection (top)
open OriginalRankedLiteralClauseHigh (highPackets highPacketShape)
open ActualFiniteOrderBranches (realized)

theorem candidateShape (known gates p positive branch) :
    ∀ q ∈ candidates known gates p positive branch, Shape q := by
  intro q used
  obtain ⟨path,member,rfl⟩ := List.mem_map.mp used
  exact (exactSymbolicPredecessorAppend (fun _ => 0) (fun _ => 0) (top branch) 0 path
    (highPacketShape branch.1 (top branch) (rankedFamily known gates p positive branch) path member)).1

theorem exactUniformHighProjectionTransport : ExactUniformHighProjectionTransport := by
  intro f θ B known gates p positive branch
  let base := realized θ branch
  let greatest := top branch
  let family := rankedFamily known gates p positive branch
  let C := cutoff B known gates p positive
  let bound := chartMinimum B θ known gates p positive branch
  let qs := highPackets branch.1 greatest family
  let guarded := candidates known gates p positive branch
  have lower := (exactActualLowerRouteFamily f base greatest C guarded (candidateShape known gates p positive branch)).2
  have route (q : Packet) (used : q ∈ qs) :
      LowerHolds f base greatest (project C (prepend greatest q)) ↔ LowerHolds f base greatest (project bound q) := by
    have shape := highPacketShape branch.1 greatest family q used
    exact (exactSymbolicPredecessorProjection f base greatest C q shape).trans
      (exactChosenRouteProjection f base greatest bound q shape).2.2.2.symm
  refine lower.symm.trans ?_
  constructor
  · rintro ⟨g,member,emit⟩
    obtain ⟨q,used,rfl⟩ := List.mem_map.mp member
    exact ⟨q,used,(route q used).mp emit⟩
  · rintro ⟨q,used,old⟩
    exact ⟨prepend greatest q,List.mem_map.mpr ⟨q,used,rfl⟩,(route q used).mpr old⟩

end LogicLineages.PermittedControl.OriginalPrintedUniformHighResidual
