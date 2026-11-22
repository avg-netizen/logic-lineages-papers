module
public import LogicLineages.PermittedControl.ActualNamedBitFamilyHighTargets
public import LogicLineages.PermittedControl.ActualRawStageCutoffTargets
public import LogicLineages.PermittedControl.OriginalPrintedRawStageQueryTargets

@[expose] public section
namespace LogicLineages.PermittedControl.StageCallbackSupplier
open OrdinalComparison
open ActualPreparedSlotAppend (Packet)
open ActualSelectedSignedRoutePacket (Shape)
open ActualBoundedSignedRoutes (PacketHolds)
open ActualSignedRouteCartesian (choices tuplePacket)
open ActualRankedNormalizationSyntax (LowerStrict)
open OriginalPrintedTerminalBitClauses (BitRow RowHolds)
open OriginalPrintedLiteralRowBridge (properClauses AdmittedOperandRow)
open OriginalRankedLiteralClauseHigh (rankedPredecessor SourceFamily)
open ActualGuardedResidualBitFamily (Family Holds reifyFamily)
open ActualBitFamilyLowSlices (coordinates dimension)
open ActualBitFamilyHigh (ranked AllPaid)
open ActualNamedBitFamilyHigh (Supplied Valid charts)
open ActualFiniteOrderBranches (Pattern)
open ActualRankChartPrototype (readWithin seed)
open ActualLowerRankChartRows (LowerChartCondition)
open OriginalPrintedPlainMatrixLinearProjection (top)
open ActualSymbolicPredecessorProjection (prepend)
open ActualGreatestRouteResidual (Residual lowerFamily)
open ActualBitFamilyRawLayout (encodeBitRow encodeFamily)
open ActualRawMixedFamilyCeiling (rowBound familyBound)
open ActualRawStageCutoff (stageBound)
open ActualBitFamilyRawDriver (HighProgram)
open ActualBitFamilyRawSemanticDriver (TypedHigh)
open OriginalPrintedRawStageQuery (HighAtStage)

/-- A per-row packet supplier: at width `r` and greatest rank `top`, one
literal bit row receives a finite list of alternative prepared packets.
Nothing is assumed about how the list is produced or ordered. -/
abbrev Supplier := Nat → Nat → BitRow → List Packet

def SupplierShape (alt : Supplier) : Prop :=
  ∀ (r top : Nat) (row : BitRow), ∀ q ∈ alt r top row, Shape q

/-- Both directions for one admitted row at one greatest value `z` and one
strict lower valuation. The payments offered to the supplier are exactly
those the executable stage bound provides: every lower rank and `z` meet
the row's own raw majorant `rowBound`, and `z` exceeds the preceding rank.
The supplier owes: the literal row holds at the updated valuation iff one
of its packets holds at that same `z` with its own tied lower table. -/
def SupplierExact (f : Nat → Nat) (B : Nat) (alt : Supplier) : Prop :=
  ∀ (r top : Nat) (baseline : Nat → Nat) (row : BitRow) (z : Nat),
    AdmittedOperandRow row →
    LowerStrict baseline top →
    (∀ t ∈ row.1.2.2, t.2.rank < r ∧ t.2.rank ≤ top) →
    (∀ i < top, rowBound B r (encodeBitRow row) ≤ baseline i) →
    max (rowBound B r (encodeBitRow row)) (rankedPredecessor top baseline) ≤ z →
    (RowHolds f (Function.update baseline top z) row ↔
      ∃ q ∈ alt r top row, PacketHolds f baseline top z q)

/-- One packet per proper clause and per Cartesian choice of one supplied
alternative for every row of that clause, joined in literal row order. -/
noncomputable def packets (alt : Supplier) (r top : Nat) (family : Family) : List Packet :=
  (properClauses family).flatMap
    (fun rows => (choices (rows.map (alt r top))).map tuplePacket)

noncomputable def outputs (alt : Supplier) (C : Nat) (family : Family) (p : Pattern) :
    List Residual :=
  lowerFamily (top p) C ((packets alt p.1 (top p) (ranked p family)).map (prepend (top p)))

noncomputable def child (alt : Supplier) (C : Nat) (family : Family) (p : Pattern) : Family :=
  reifyFamily C (top p) (outputs alt C family p)

noncomputable def compile (alt : Supplier) (C : Nat) (family : Family) (names : List Nat) :
    List (Pattern × Family) :=
  (charts names).map (fun p => (p,child alt C family p))

/-- The ordered typed children at the executable stage bound and on the
executable sorted name list of the encoded family itself. -/
noncomputable def stageChildren (alt : Supplier) (B : Nat) : TypedHigh :=
  fun fs =>
    (compile alt (stageBound B (encodeFamily fs)) fs
      (ActualBitFamilyRawLayout.names (encodeFamily fs))).map Prod.snd

/-- The literal emission equation asked of a raw high program. It is an
equation between encoded lists only; it carries no semantic content. -/
def Emits (alt : Supplier) (B : Nat) (high : HighProgram) : Prop :=
  ∀ fs : Family, 0 < dimension fs →
    high (stageBound B (encodeFamily fs),encodeFamily fs) =
      (stageChildren alt B fs).map encodeFamily

/-- Every valid chart's ranked family has its raw majorant below `C`. -/
def RawPaid (B C : Nat) (family : Family) (names : List Nat) : Prop :=
  ∀ p ∈ charts names, familyBound B p.1 (encodeFamily (ranked p family)) ≤ C

def ExactSuppliedPacketShape : Prop :=
  ∀ (alt : Supplier), SupplierShape alt →
    ∀ (r top : Nat) (family : Family), ∀ q ∈ packets alt r top family, Shape q

/-- All rows of one clause are compared at the one shared greatest value;
each chosen tuple is one joined packet with one tied lower table. -/
def ExactSuppliedRankedPoint : Prop :=
  ∀ (f : Nat → Nat) (B : Nat) (alt : Supplier), SupplierShape alt → SupplierExact f B alt →
    ∀ (r top : Nat) (baseline : Nat → Nat) (family : Family) (z : Nat),
      LowerStrict baseline top →
      (∀ rows ∈ family, ∀ row ∈ rows, ∀ t ∈ row.1.2.2, t.2.rank < r ∧ t.2.rank ≤ top) →
      (∀ i < top, familyBound B r (encodeFamily family) ≤ baseline i) →
      max (familyBound B r (encodeFamily family)) (rankedPredecessor top baseline) ≤ z →
      (SourceFamily f (Function.update baseline top z) family ↔
        ∃ q ∈ packets alt r top family, PacketHolds f baseline top z q)

def ExactSuppliedUniformChartChild : Prop :=
  ∀ (f : Nat → Nat) (B C : Nat) (alt : Supplier), SupplierShape alt → SupplierExact f B alt →
    ∀ (family : Family) (names : List Nat), Supplied family names → RawPaid B C family names →
    ∀ p : Pattern, Valid names p → ∀ (lower outside : Nat → Nat),
      (Holds f lower (child alt C family p) ↔
        LowerChartCondition C (top p) lower ∧
        ∃ z : Nat, seed C p lower ≤ z ∧
          AllPaid C family (readWithin names p lower outside z) ∧
          Holds f (readWithin names p lower outside z) family)

def ExactSuppliedHighExistential : Prop :=
  ∀ (f : Nat → Nat) (B C : Nat) (alt : Supplier), SupplierShape alt → SupplierExact f B alt →
    ∀ (family : Family) (names : List Nat), Supplied family names → RawPaid B C family names →
      0 < dimension family →
      ((∃ θ : Nat → Nat, AllPaid C family θ ∧ Holds f θ family) ↔
        ∃ result ∈ compile alt C family names, ∃ lower : Nat → Nat, Holds f lower result.2)

def ExactSuppliedHighDimension : Prop :=
  ∀ (alt : Supplier), SupplierShape alt →
    ∀ (C : Nat) (family : Family) (names : List Nat), Supplied family names →
    ∀ result ∈ compile alt C family names,
      (∀ k ∈ coordinates result.2, k < top result.1) ∧ dimension result.2 < dimension family

/-- The high callback contract of the stage query, both directions, at the
executable stage bound, for every exact supplier and every raw program
that emits the encoded children. No selection hypothesis beyond what
`SupplierExact` itself carries. -/
def ExactSuppliedStageCallback : Prop :=
  ∀ (f : Nat → Nat) (B : Nat) (alt : Supplier), SupplierShape alt → SupplierExact f B alt →
    ∀ high : HighProgram, Emits alt B high → HighAtStage f B high (stageChildren alt B)

def FullStageCallbackSupplier : Prop :=
  ExactSuppliedPacketShape ∧ ExactSuppliedRankedPoint ∧ ExactSuppliedUniformChartChild ∧
    ExactSuppliedHighExistential ∧ ExactSuppliedHighDimension ∧ ExactSuppliedStageCallback

end LogicLineages.PermittedControl.StageCallbackSupplier
