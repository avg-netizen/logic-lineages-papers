module
public import LogicLineages.PermittedControl.ActualSignedRouteCartesianTargets
public import LogicLineages.PermittedControl.ActualGreatestCongruenceRouteTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualPaidMixedMatrixTuples
open OrdinalComparison
open ActualPreparedSlotAppend (Packet)
open ActualSelectedSignedRoutePacket (Shape)
open ActualSignedRouteCartesian (SignedRow rowPackets choices tuplePacket)
open ActualPaidSignedRouteReplay (SourceHolds LowerSetup replayMinimum)
open ActualGreatestCongruenceRoute (SourceCongruence LowerModulusSetup modulusMinimum)
open ActualSymbolicZeroSuccessor (SyntaxState)
open ActualBoundedSignedRoutes (PacketHolds)

inductive MixedRow where
  | signed (row : SignedRow)
  | modular (modulus : Nat) (source : SyntaxState) (positive : Bool)

def Source (f ρ : Nat → Nat) : MixedRow → Prop
  | .signed row => SourceHolds f ρ row.source row.test row.positive
  | .modular m s positive => SourceCongruence f ρ m s positive

def Ready (B r top : Nat) (baseline : Nat → Nat) : MixedRow → Prop
  | .signed row => LowerSetup B r top baseline row.source
  | .modular m s _ => LowerModulusSetup B top m baseline s

noncomputable def rowMinimum (B r top : Nat) (baseline : Nat → Nat) : MixedRow → Nat
  | .signed row => replayMinimum B r top baseline row.source
  | .modular m s _ => modulusMinimum B m s

noncomputable def matrixMinimum (B r top : Nat) (baseline : Nat → Nat) (rows : List MixedRow) : Nat :=
  rows.foldr (fun row n => max (rowMinimum B r top baseline row) n) 0

noncomputable def alternatives (r top : Nat) : MixedRow → List Packet
  | .signed row => rowPackets r top row
  | .modular m s positive => [ActualGreatestCongruenceRoute.packet top m s positive]

noncomputable def tuples (r top : Nat) (rows : List MixedRow) : List (List Packet) :=
  choices (rows.map (alternatives r top))

def MatrixSource (f ρ : Nat → Nat) (rows : List MixedRow) : Prop :=
  ∀ row ∈ rows, Source f ρ row

def ExactMixedMatrixMinimum : Prop :=
  ∀ (B r top : Nat) (baseline : Nat → Nat) (rows : List MixedRow) (z : Nat),
    matrixMinimum B r top baseline rows ≤ z ↔ ∀ row ∈ rows, rowMinimum B r top baseline row ≤ z

def ExactPaidMixedRow : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
    ∀ (r top : Nat) (baseline : Nat → Nat) (row : MixedRow),
      Ready B r top baseline row → ∀ z : Nat, rowMinimum B r top baseline row ≤ z →
        (Source f (Function.update baseline top z) row ↔
          ∃ q ∈ alternatives r top row, PacketHolds f baseline top z q)

def ExactMixedTupleShape : Prop :=
  ∀ (r top : Nat) (rows : List MixedRow),
    ∀ selected ∈ tuples r top rows, Shape (tuplePacket selected)

/-- Every source row is compared at the one genuine original raw update.
No individually projected existential witnesses are combined. -/
def ExactPaidMixedMatrixTuples : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
    ∀ (r top : Nat) (baseline : Nat → Nat) (rows : List MixedRow),
      (∀ row ∈ rows, Ready B r top baseline row) →
      ∀ z : Nat, matrixMinimum B r top baseline rows ≤ z →
        (MatrixSource f (Function.update baseline top z) rows ↔
          ∃ selected ∈ tuples r top rows, PacketHolds f baseline top z (tuplePacket selected))

def FullActualPaidMixedMatrixTuples : Prop :=
  ExactMixedMatrixMinimum ∧ ExactPaidMixedRow ∧ ExactMixedTupleShape ∧ ExactPaidMixedMatrixTuples

end LogicLineages.PermittedControl.ActualPaidMixedMatrixTuples
