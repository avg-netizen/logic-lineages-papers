module
public import LogicLineages.PermittedControl.ActualSelectedSignedRoutePacketTargets
public import LogicLineages.PermittedControl.ActualPaidSignedRouteReplayTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualSignedRouteCartesian
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open ActualPreparedSlotAppend (Packet append)
open ActualSelectedSignedRoutePacket (Shape packet)
open ActualSignedOrdinaryPairHigh (OrderTest)
open ActualBoundedSignedRoutes (PacketHolds RouteHolds routes)
open ActualSymbolicZeroSuccessor (SyntaxState)
open ActualSyntaxChargeBudget (syntaxBudget)

structure SignedRow where
  source : SyntaxState
  test : OrderTest
  positive : Bool

def choices : List (List Packet) → List (List Packet)
  | [] => [[]]
  | row::rows => row.flatMap (fun p => (choices rows).map (List.cons p))

def tuplePacket (positions : List Packet) : Packet := positions.foldr append ([],.truth)

noncomputable def rowPackets (r top : Nat) (row : SignedRow) : List Packet :=
  (routes top row.test row.positive (syntaxBudget r row.source.terms) row.source).map
    (packet row.test row.positive)

noncomputable def matrixTuples (r top : Nat) (rows : List SignedRow) : List (List Packet) :=
  choices (rows.map (rowPackets r top))

def RowHolds (f baseline : Nat → Nat) (r top z : Nat) (row : SignedRow) : Prop :=
  ∃ path ∈ routes top row.test row.positive (syntaxBudget r row.source.terms) row.source,
    RouteHolds f baseline top z row.test row.positive path

def ExactTupleChoice : Prop :=
  ∀ (rows : List (List Packet)) (positions : List Packet),
    positions ∈ choices rows ↔ List.Forall₂ (fun p row => p ∈ row) positions rows

def ExactCartesianPacketEval : Prop :=
  ∀ (f baseline : Nat → Nat) (top z : Nat) (rows : List (List Packet)),
    (∀ row ∈ rows, ∀ p ∈ row, Shape p) →
      (∀ positions ∈ choices rows, Shape (tuplePacket positions)) ∧
      ((∃ positions ∈ choices rows, PacketHolds f baseline top z (tuplePacket positions)) ↔
        ∀ row ∈ rows, ∃ p ∈ row, PacketHolds f baseline top z p)

/-- One common numerical value and one tied table per tuple. There is
no elimination of individual rows before these witnesses are joined. -/
def ExactActualSignedMatrixTuples : Prop :=
  ∀ (f baseline : Nat → Nat) (r top z : Nat) (rows : List SignedRow),
    (∀ positions ∈ matrixTuples r top rows, Shape (tuplePacket positions)) ∧
    ((∃ positions ∈ matrixTuples r top rows,
        PacketHolds f baseline top z (tuplePacket positions)) ↔
      ∀ row ∈ rows, RowHolds f baseline r top z row)

def FullActualSignedRouteCartesian : Prop :=
  ExactTupleChoice ∧ ExactCartesianPacketEval ∧ ExactActualSignedMatrixTuples

end LogicLineages.PermittedControl.ActualSignedRouteCartesian
