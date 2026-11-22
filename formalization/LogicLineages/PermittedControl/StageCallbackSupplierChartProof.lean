module
public import LogicLineages.PermittedControl.StageCallbackSupplierTargets
import LogicLineages.PermittedControl.StageCallbackSupplierPointProof
import LogicLineages.PermittedControl.ActualBitFamilyHighRankProof
import LogicLineages.PermittedControl.ActualNamedBitFamilyHighSetupProof
import LogicLineages.PermittedControl.ActualGreatestRouteResidualProof
import LogicLineages.PermittedControl.ActualSymbolicPredecessorProjectionProof
import LogicLineages.PermittedControl.ActualGuardedResidualBitFamilyProof
import LogicLineages.PermittedControl.ActualLowerRankChartRowsProof

@[expose] public section
namespace LogicLineages.PermittedControl.StageCallbackSupplier
open OrdinalComparison
open ActualGuardedResidualBitFamily (Family Holds exactGuardedResidualUnion)
open ActualBitFamilyLowSlices (coordinates)
open ActualFiniteOrderBranches (Pattern rename)
open ActualRankChartPrototype (readWithin seed)
open ActualLowerRankChartRows (LowerChartCondition exactLowerRankChartRows lowerChart)
open OriginalPrintedPlainMatrixLinearProjection (top)
open OriginalRankedLiteralClauseHigh (rankedPredecessor)
open ActualSymbolicPredecessorProjection (prepend exactSymbolicPredecessorAppend
  exactSymbolicPredecessorProjection)
open ActualSelectedSignedRoutePacket (Shape)
open ActualSelectedSignedRouteProjection (project LowerHolds)
open ActualGreatestRouteResidual (Residual rows exactActualLowerRouteFamily)
open ActualPreparedSlotAppend (Packet)
open ActualBoundedSignedRoutes (PacketHolds)
open ActualBitFamilyHigh (ranked renameBit AllPaid exactGenericRankTransport sourceCoordinate)
open ActualNamedBitFamilyHigh (Supplied Valid charts renameIndex exactNamedCharts)
open ActualBitFamilyRawLayout (encodeFamily)
open ActualRawMixedFamilyCeiling (familyBound)

theorem amendedShapes (alt : Supplier) (shaped : SupplierShape alt) (p : Pattern) (family : Family) :
    ∀ q ∈ (packets alt p.1 (top p) (ranked p family)).map (prepend (top p)), Shape q := by
  intro q member
  obtain ⟨src,old,rfl⟩ := List.mem_map.mp member
  exact (exactSymbolicPredecessorAppend (fun _ => 0) (fun _ => 0) (top p) 0 src
    (exactSuppliedPacketShape alt shaped p.1 (top p) (ranked p family) src old)).1

theorem namedScope (family : Family) (names : List Nat) (p : Pattern)
    (support : Supplied family names) (good : Valid names p) :
    ∀ clause ∈ ranked p family, ∀ r ∈ clause, ∀ t ∈ r.1.2.2, t.2.rank < p.1 := by
  intro clause used r inRow t inTerm
  obtain ⟨source,atSource,rfl⟩ := List.mem_map.mp used
  obtain ⟨row,atRow,rfl⟩ := List.mem_map.mp inRow
  obtain ⟨raw,atRaw,rfl⟩ := List.mem_map.mp inTerm
  have bound := renameIndex names p good raw.2.rank
    ((support.2 _).mpr (sourceCoordinate family source atSource row atRow raw atRaw))
  rcases raw with ⟨w,op⟩
  cases op <;> exact bound

theorem rankReads (family : Family) (names : List Nat) (p : Pattern)
    (support : Supplied family names) (good : Valid names p)
    (C : Nat) (lower outside : Nat → Nat) (chart : LowerChartCondition C (top p) lower)
    (z : Nat) (cut : seed C p lower ≤ z) :
    AllPaid C family (readWithin names p lower outside z) := by
  intro n used
  have present : n ∈ names := (support.2 n).mpr used
  have scope : rename p n ≤ top p := by
    have lt := renameIndex names p good n present
    change rename p n ≤ p.1-1
    omega
  rw [readWithin,if_pos present]
  rcases lt_or_eq_of_le scope with smaller | greatest
  · rw [Function.update_of_ne (ne_of_lt smaller)]
    exact chart.1 _ smaller
  · rw [greatest,Function.update_self]
    exact (le_max_left _ _).trans cut

/-- Projection happens after the join: each residual is the projection of
one whole joined packet, at one greatest value above the common seed. -/
theorem residualPacket (alt : Supplier) (shaped : SupplierShape alt) (f lower : Nat → Nat)
    (C : Nat) (family : Family) (p : Pattern) :
    (∃ out ∈ outputs alt C family p, ActualGreatestRouteResidual.LowerMatrix f lower out) ↔
      ∃ z : Nat, seed C p lower ≤ z ∧
        ∃ q ∈ packets alt p.1 (top p) (ranked p family), PacketHolds f lower (top p) z q := by
  have reduction := (exactActualLowerRouteFamily f lower (top p) C
    ((packets alt p.1 (top p) (ranked p family)).map (prepend (top p)))
    (amendedShapes alt shaped p family)).2
  refine reduction.symm.trans ?_
  constructor
  · rintro ⟨output,atOutput,lifted⟩
    obtain ⟨q,used,rfl⟩ := List.mem_map.mp atOutput
    have shape := exactSuppliedPacketShape alt shaped p.1 (top p) (ranked p family) q used
    obtain ⟨z,high,passes⟩ :=
      (exactSymbolicPredecessorProjection f lower (top p) C q shape).mp lifted
    exact ⟨z,high,q,used,passes⟩
  · rintro ⟨z,high,q,used,passes⟩
    have shape := exactSuppliedPacketShape alt shaped p.1 (top p) (ranked p family) q used
    exact ⟨prepend (top p) q,List.mem_map.mpr ⟨q,used,rfl⟩,
      (exactSymbolicPredecessorProjection f lower (top p) C q shape).mpr ⟨z,high,passes⟩⟩

theorem exactSuppliedUniformChartChild : ExactSuppliedUniformChartChild := by
  intro f B C alt shaped rowwise family names support paid p good lower outside
  have chart := (exactLowerRankChartRows f lower C (top p)).1
  have decode := (exactGuardedResidualUnion f lower C (top p) (outputs alt C family p)).2
  have static : familyBound B p.1 (encodeFamily (ranked p family)) ≤ C :=
    paid p ((exactNamedCharts names p).mpr good)
  have sourceScope := namedScope family names p support good
  have source (funded : LowerChartCondition C (top p) lower) (z : Nat)
      (within : seed C p lower ≤ z) :
      (∃ q ∈ packets alt p.1 (top p) (ranked p family), PacketHolds f lower (top p) z q) ↔
      Holds f (readWithin names p lower outside z) family := by
    have same (k : Nat) (used : k ∈ coordinates family) :
        Function.update lower (top p) z (rename p k) = readWithin names p lower outside z k := by
      have named : k ∈ names := (support.2 k).mpr used
      rw [readWithin,if_pos named]
    have inChart : ∀ rows ∈ ranked p family, ∀ row ∈ rows, ∀ t ∈ row.1.2.2,
        t.2.rank < p.1 ∧ t.2.rank ≤ top p := by
      intro c hc row hr t ht
      have h := sourceScope c hc row hr t ht
      exact ⟨h,by change t.2.rank ≤ p.1-1; omega⟩
    have point := exactSuppliedRankedPoint f B alt shaped rowwise p.1 (top p) lower
      (ranked p family) z funded.2 inChart
      (fun i below => static.trans (funded.1 i below))
      (max_le (static.trans ((le_max_left _ _).trans within)) ((le_max_right _ _).trans within))
    exact point.symm.trans
      (exactGenericRankTransport f (readWithin names p lower outside z)
        (Function.update lower (top p) z) family p same).symm
  constructor
  · intro hold
    obtain ⟨out,inOut,lowerGuard,lowerData⟩ := decode.mp hold
    have ready := chart.mp lowerGuard
    obtain ⟨z,high,q,used,passes⟩ :=
      (residualPacket alt shaped f lower C family p).mp ⟨out,inOut,lowerData⟩
    exact ⟨ready,z,high,rankReads family names p support good C lower outside ready z high,
      (source ready z high).mp ⟨q,used,passes⟩⟩
  · rintro ⟨ready,z,high,_,actual⟩
    obtain ⟨out,member,lowers⟩ :=
      (residualPacket alt shaped f lower C family p).mpr ⟨z,high,(source ready z high).mpr actual⟩
    exact decode.mpr ⟨out,member,chart.mpr ready,lowers⟩

end LogicLineages.PermittedControl.StageCallbackSupplier
