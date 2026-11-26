module
public import LogicLineages.PermittedControl.ActualSymbolicPredecessorProjectionTargets
import LogicLineages.PermittedControl.ActualSymbolicPredecessorProjectionGuardProof
import LogicLineages.PermittedControl.ActualSelectedSignedRoutePacketFoldProof
import LogicLineages.PermittedControl.ActualSelectedSignedRouteProjectionChosenProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualSymbolicPredecessorProjection
open ActualSelectedSignedRouteProjection (exactChosenRouteProjection)
open ActualSelectedSignedRoutePacket (exactRouteAppend)
open OriginalRankedLiteralClauseHigh (rankedPredecessor)

theorem exactSymbolicPredecessorAppend : ExactSymbolicPredecessorAppend := by
  intro f baseline top z p safe
  by_cases zero : top = 0
  · simpa only [prepend,rankedPredecessor,if_pos zero,Nat.zero_le,true_and] using
      (show ActualSelectedSignedRoutePacket.Shape p ∧
        (ActualBoundedSignedRoutes.PacketHolds f baseline top z p ↔
          ActualBoundedSignedRoutes.PacketHolds f baseline top z p) from ⟨safe,Iff.rfl⟩)
  · rw [prepend,if_neg zero,rankedPredecessor,if_neg zero]
    have guard := exactSymbolicPredecessorGuard f baseline top z (Nat.pos_of_ne_zero zero)
    have both := exactRouteAppend f baseline top z (predecessorPacket top) p guard.1 safe
    exact ⟨both.1,both.2.trans (and_congr guard.2 Iff.rfl)⟩

theorem exactSymbolicPredecessorProjection : ExactSymbolicPredecessorProjection := by
  intro f baseline top cutoff p safe
  have step (z : Nat) := exactSymbolicPredecessorAppend f baseline top z p safe
  have elimination := (exactChosenRouteProjection f baseline top cutoff
    (prepend top p) (step 0).1).2.2.2
  refine elimination.trans ?_
  constructor
  · rintro ⟨z,which,passes⟩
    obtain ⟨before,holds⟩ := (step z).2.mp passes
    exact ⟨z,max_le which before,holds⟩
  · rintro ⟨z,which,holds⟩
    have cutoffPaid : cutoff ≤ z := (le_max_left _ _).trans which
    have before : rankedPredecessor top baseline ≤ z := (le_max_right _ _).trans which
    exact ⟨z,cutoffPaid,(step z).2.mpr ⟨before,holds⟩⟩

end LogicLineages.PermittedControl.ActualSymbolicPredecessorProjection
