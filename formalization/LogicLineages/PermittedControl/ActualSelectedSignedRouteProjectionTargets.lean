module
public import LogicLineages.PermittedControl.ActualSelectedSignedRoutePacketTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualSelectedSignedRouteProjection
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open PreparedProjection
open ActualPreparedSlotAppend (Packet append)
open ActualSelectedSignedRoutePacket (Shape packet)
open ActualSignedOrdinaryPairHigh (OrderTest)
open ActualBoundedSignedRoutes (PacketHolds RouteHolds routes)
open ActualSymbolicZeroSuccessor (SyntaxState)

def cutoffPacket (minimum : Nat) : Packet :=
  ([],.atom (.nonnegative (-(minimum : Int),[(1,.variable 0)])))

def bounded (minimum : Nat) (p : Packet) : Packet := append (cutoffPacket minimum) p

def project (minimum : Nat) (p : Packet) : Packet :=
  let q := bounded minimum p
  (q.1,eliminatePreparedFormula q.2)

def LowerHolds (f baseline : Nat → Nat) (top : Nat) (p : Packet) : Prop :=
  ∃ ν : Nat → Nat, PreparedTableTied f top baseline p.1 ν ∧ p.2.eval ν

def ExactChosenRouteProjection : Prop :=
  ∀ (f baseline : Nat → Nat) (top minimum : Nat) (p : Packet),
    Shape p →
    (project minimum p).1 = p.1 ∧ Shape (project minimum p) ∧
    (∀ n ∈ (project minimum p).2.variables, 0 < n) ∧
    (LowerHolds f baseline top (project minimum p) ↔
      ∃ z : Nat, minimum ≤ z ∧ PacketHolds f baseline top z p)

/-- Each alternative retains its own actual lower table. The exterior
prior can be transported only if its explicit replay law is paid. -/
def ExactSignedRouteUnionProjection : Prop :=
  ∀ (f baseline : Nat → Nat) (top minimum fuel : Nat) (test : OrderTest) (positive : Bool)
    (s : SyntaxState) (prior : (Nat → Nat) → Prop),
    (∀ z : Nat, minimum ≤ z → (prior (Function.update baseline top z) ↔ prior baseline)) →
    ((prior baseline ∧ ∃ path ∈ routes top test positive fuel s,
        LowerHolds f baseline top (project minimum (packet test positive path))) ↔
      ∃ z : Nat, minimum ≤ z ∧ prior (Function.update baseline top z) ∧
        ∃ path ∈ routes top test positive fuel s, RouteHolds f baseline top z test positive path)

def FullActualSelectedSignedRouteProjection : Prop :=
  ExactChosenRouteProjection ∧ ExactSignedRouteUnionProjection

end LogicLineages.PermittedControl.ActualSelectedSignedRouteProjection
