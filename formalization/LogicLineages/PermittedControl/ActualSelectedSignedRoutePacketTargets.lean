module
public import LogicLineages.PermittedControl.ActualBoundedSignedRoutesTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualSelectedSignedRoutePacket
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open PreparedProjection
open ActualPreparedSlotAppend (Packet append)
open ActualSignedOrdinaryPairHigh (OrderTest)
open ActualBoundedSignedRoutes (Tip Route PacketHolds RouteHolds routes)
open ActualSymbolicZeroSuccessor (SyntaxState)

def signedBit : OrderTest → Int → Bool
  | .equalZero,c => decide (c = 0)
  | .nonnegative,c => decide (0 ≤ c)
  | .positive,c => decide (0 < c)

def terminalPacket (test : OrderTest) (positive : Bool) : Tip → Packet
  | .linear p => p
  | .signed c => ([], if (if positive then signedBit test c else !(signedBit test c))
                   then .truth else .falsity)

/-- Only this route's guards, in literal order, followed by its one
terminal. The reserved raw coordinate stays zero at every append. -/
def packet (test : OrderTest) (positive : Bool) (path : Route) : Packet :=
  path.guards.foldr append (terminalPacket test positive path.tip)

def Shape (p : Packet) : Prop := PreparedInput p.1 p.2

def ExactRouteAppend : Prop :=
  ∀ (f baseline : Nat → Nat) (top z : Nat) (l r : Packet), Shape l → Shape r →
    Shape (append l r) ∧
      (PacketHolds f baseline top z (append l r) ↔
        PacketHolds f baseline top z l ∧ PacketHolds f baseline top z r)

def ExactSelectedRoutePacket : Prop :=
  ∀ (f baseline : Nat → Nat) (top z : Nat) (test : OrderTest) (positive : Bool)
    (path : Route),
    (∀ p ∈ path.guards, Shape p) → Shape (terminalPacket test positive path.tip) →
      Shape (packet test positive path) ∧
      (PacketHolds f baseline top z (packet test positive path) ↔
        RouteHolds f baseline top z test positive path) ∧
      ∀ (ν : Nat → Nat), PreparedTableTied f top baseline (packet test positive path).1 ν →
        ∀ (j : Nat) (hj : j < (packet test positive path).1.length),
          lowerOperandRead f baseline (packet test positive path).1[j] = some (some (ν (j+1)))

/-- Shape only, not liveness: discarded or unrealizable syntactic routes
need not have any actual tied assignments. -/
def ExactEmittedRouteShape : Prop :=
  ∀ (top fuel : Nat) (test : OrderTest) (positive : Bool) (s : SyntaxState) (path : Route),
    path ∈ routes top test positive fuel s →
    (∀ p ∈ path.guards, Shape p) ∧ Shape (terminalPacket test positive path.tip)

def ExactEmittedRouteFamily : Prop :=
  ∀ (f baseline : Nat → Nat) (top z fuel : Nat) (test : OrderTest) (positive : Bool)
    (s : SyntaxState),
    (∀ path ∈ routes top test positive fuel s, Shape (packet test positive path)) ∧
    ((∃ path ∈ routes top test positive fuel s, PacketHolds f baseline top z (packet test positive path)) ↔
     (∃ path ∈ routes top test positive fuel s, RouteHolds f baseline top z test positive path))

def FullActualSelectedSignedRoutePacket : Prop :=
  ExactRouteAppend ∧ ExactSelectedRoutePacket ∧ ExactEmittedRouteShape ∧ ExactEmittedRouteFamily

end LogicLineages.PermittedControl.ActualSelectedSignedRoutePacket
