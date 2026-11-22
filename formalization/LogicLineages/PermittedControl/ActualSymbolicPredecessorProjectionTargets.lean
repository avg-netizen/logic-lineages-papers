module
public import LogicLineages.PermittedControl.ActualSelectedSignedRouteProjectionTargets
public import LogicLineages.PermittedControl.OriginalRankedLiteralClauseHighTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualSymbolicPredecessorProjection
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open ActualPreparedSlotAppend (Packet append)
open ActualSelectedSignedRoutePacket (Shape)
open ActualSelectedSignedRouteProjection (project LowerHolds)
open ActualBoundedSignedRoutes (PacketHolds)
open OriginalRankedLiteralClauseHigh (rankedPredecessor)

def predecessorPacket (top : Nat) : Packet :=
  ([.coordinate (top-1)],.atom (.nonnegative (-1,[(1,.variable 0),(-1,.variable 1)])))

/-- The predecessor remains a symbolic real bare lower slot. Nothing
from the actual baseline valuation appears in this output syntax. -/
def prepend (top : Nat) (p : Packet) : Packet :=
  if top = 0 then p else append (predecessorPacket top) p

def ExactSymbolicPredecessorGuard : Prop :=
  ∀ (f baseline : Nat → Nat) (top z : Nat), 0 < top →
    Shape (predecessorPacket top) ∧
    (PacketHolds f baseline top z (predecessorPacket top) ↔ baseline (top-1)+1 ≤ z)

def ExactSymbolicPredecessorAppend : Prop :=
  ∀ (f baseline : Nat → Nat) (top z : Nat) (p : Packet), Shape p →
    Shape (prepend top p) ∧
      (PacketHolds f baseline top z (prepend top p) ↔
        rankedPredecessor top baseline ≤ z ∧ PacketHolds f baseline top z p)

def ExactSymbolicPredecessorProjection : Prop :=
  ∀ (f baseline : Nat → Nat) (top cutoff : Nat) (p : Packet), Shape p →
    (LowerHolds f baseline top (project cutoff (prepend top p)) ↔
      ∃ z : Nat, max cutoff (rankedPredecessor top baseline) ≤ z ∧ PacketHolds f baseline top z p)

def FullActualSymbolicPredecessorProjection : Prop :=
  ExactSymbolicPredecessorGuard ∧ ExactSymbolicPredecessorAppend ∧ ExactSymbolicPredecessorProjection

end LogicLineages.PermittedControl.ActualSymbolicPredecessorProjection
