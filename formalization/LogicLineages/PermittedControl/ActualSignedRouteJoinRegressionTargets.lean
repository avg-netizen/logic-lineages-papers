module
public import LogicLineages.PermittedControl.ActualSignedRouteCartesianTargets
public import LogicLineages.PermittedControl.ActualSymbolicPredecessorProjectionTargets
public import LogicLineages.PermittedControl.ActualGreatestRouteResidualTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualSignedRouteJoinRegression
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open PreparedProjection
open ActualPreparedSlotAppend (Packet)
open ActualSelectedSignedRoutePacket (Shape)
open ActualBoundedSignedRoutes (PacketHolds)
open ActualSignedRouteCartesian (choices tuplePacket)
open ActualSelectedSignedRouteProjection (project LowerHolds)
open ActualSymbolicPredecessorProjection (prepend)
open OriginalRankedLiteralClauseHigh (rankedPredecessor)
open ActualGreatestRouteResidual (lowerFamily LowerMatrix StrictLower)

/-- The shared greatest coordinate (reserved name zero) is at least `c`. -/
def atLeastRow (c : Nat) : NormalForm.Formula :=
  .atom (.nonnegative (-(c : Int),[(1,.variable 0)]))

/-- The shared greatest coordinate (reserved name zero) is at most `c`. -/
def atMostRow (c : Nat) : NormalForm.Formula :=
  .atom (.nonnegative ((c : Int),[(-1,.variable 0)]))

/-- One row's packet: its own lower table `ops`, and two literal rows that
force the shared greatest coordinate to be exactly `c`. -/
def pinned (ops : List LowerOperand) (c : Nat) : Packet :=
  (ops,.conjunction (atLeastRow c) (atMostRow c))

/-- Each row packet alone holds exactly at its own value, with any tied table. -/
def ExactPinnedPacket : Prop :=
  ∀ (f baseline : Nat → Nat) (top z c : Nat) (ops : List LowerOperand),
    Shape (pinned ops c) ∧
    (PacketHolds f baseline top z (pinned ops c) ↔
      z = c ∧ ∃ ν : Nat → Nat, PreparedTableTied f top baseline ops ν)

/-- The join (Cartesian choice and `tuplePacket`) of the row forcing the
cutoff `C` with the row forcing `C+1` holds at no shared value and no tied
table, whatever the two lower tables are. -/
def JoinedPacketUnsatisfiable : Prop :=
  ∀ (f baseline : Nat → Nat) (top C : Nat) (ops₁ ops₂ : List LowerOperand),
    Shape (tuplePacket [pinned ops₁ C,pinned ops₂ (C+1)]) ∧
    (∀ z : Nat, ¬ PacketHolds f baseline top z (tuplePacket [pinned ops₁ C,pinned ops₂ (C+1)])) ∧
    ¬ ∃ z : Nat, ∃ positions ∈ choices [[pinned ops₁ C],[pinned ops₂ (C+1)]],
        PacketHolds f baseline top z (tuplePacket positions)

/-- Projected separately at the cutoff, each row is satisfiable (also after
the symbolic predecessor guard, when the predecessor is below the cutoff). -/
def ProjectedSinglesSatisfiable : Prop :=
  ∀ (f baseline : Nat → Nat) (top C : Nat) (ops : List LowerOperand),
    (∃ ν : Nat → Nat, PreparedTableTied f top baseline ops ν) →
      LowerHolds f baseline top (project C (pinned ops C)) ∧
      LowerHolds f baseline top (project C (pinned ops (C+1))) ∧
      (rankedPredecessor top baseline ≤ C →
        LowerHolds f baseline top (project C (prepend top (pinned ops C))) ∧
        LowerHolds f baseline top (project C (prepend top (pinned ops (C+1)))))

/-- Projecting after the join keeps the shared-coordinate constraint: the
projected joined packet is unsatisfiable, with or without the predecessor guard. -/
def ProjectedJoinUnsatisfiable : Prop :=
  ∀ (f baseline : Nat → Nat) (top C : Nat) (ops₁ ops₂ : List LowerOperand),
    ¬ LowerHolds f baseline top (project C (tuplePacket [pinned ops₁ C,pinned ops₂ (C+1)])) ∧
    ¬ LowerHolds f baseline top
        (project C (prepend top (tuplePacket [pinned ops₁ C,pinned ops₂ (C+1)])))

/-- In the residual family: the joined packet is emitted (exactly one
decoded residual, not filtered away) and that residual is unsatisfiable. -/
def LowerFamilyJoinUnsatisfiable : Prop :=
  ∀ (f ρ : Nat → Nat) (top C : Nat) (ops₁ ops₂ : List LowerOperand),
    (StrictLower top ops₁ → StrictLower top ops₂ →
      (lowerFamily top C [prepend top (tuplePacket [pinned ops₁ C,pinned ops₂ (C+1)])]).length = 1) ∧
    ∀ p ∈ lowerFamily top C [prepend top (tuplePacket [pinned ops₁ C,pinned ops₂ (C+1)])],
      ¬ LowerMatrix f ρ p

/-- In the residual family, each row alone has a satisfied residual. -/
def LowerFamilySinglesSatisfiable : Prop :=
  ∀ (f ρ : Nat → Nat) (top C : Nat) (ops : List LowerOperand),
    (∃ ν : Nat → Nat, PreparedTableTied f top ρ ops ν) → rankedPredecessor top ρ ≤ C →
      (∃ p ∈ lowerFamily top C [prepend top (pinned ops C)], LowerMatrix f ρ p) ∧
      (∃ p ∈ lowerFamily top C [prepend top (pinned ops (C+1))], LowerMatrix f ρ p)

/-- A one-slot lower table of a strictly lower raw coordinate is always tied. -/
def CoordinateTableLive : Prop :=
  ∀ (f ρ : Nat → Nat) (top k : Nat), k < top →
    ∃ ν : Nat → Nat, PreparedTableTied f top ρ [.coordinate k] ν

/-- Headline regression at one nonempty lower table per row (so the right
packet is genuinely shifted by the join), every control `f`, every baseline. -/
def JoinRegression : Prop :=
  ∀ (f ρ : Nat → Nat) (top k C : Nat), k < top → rankedPredecessor top ρ ≤ C →
    (∃ p ∈ lowerFamily top C [prepend top (pinned [.coordinate k] C)], LowerMatrix f ρ p) ∧
    (∃ p ∈ lowerFamily top C [prepend top (pinned [.coordinate k] (C+1))], LowerMatrix f ρ p) ∧
    (lowerFamily top C
      [prepend top (tuplePacket [pinned [.coordinate k] C,pinned [.coordinate k] (C+1)])]).length = 1 ∧
    (∀ p ∈ lowerFamily top C
      [prepend top (tuplePacket [pinned [.coordinate k] C,pinned [.coordinate k] (C+1)])],
        ¬ LowerMatrix f ρ p) ∧
    LowerHolds f ρ top (project C (pinned [.coordinate k] C)) ∧
    LowerHolds f ρ top (project C (pinned [.coordinate k] (C+1))) ∧
    ¬ LowerHolds f ρ top (project C (tuplePacket [pinned [.coordinate k] C,pinned [.coordinate k] (C+1)])) ∧
    ∀ z : Nat, ¬ PacketHolds f ρ top z (tuplePacket [pinned [.coordinate k] C,pinned [.coordinate k] (C+1)])

def FullActualSignedRouteJoinRegression : Prop :=
  ExactPinnedPacket ∧ JoinedPacketUnsatisfiable ∧ ProjectedSinglesSatisfiable ∧
    ProjectedJoinUnsatisfiable ∧ LowerFamilyJoinUnsatisfiable ∧ LowerFamilySinglesSatisfiable ∧
    CoordinateTableLive ∧ JoinRegression

end LogicLineages.PermittedControl.ActualSignedRouteJoinRegression
