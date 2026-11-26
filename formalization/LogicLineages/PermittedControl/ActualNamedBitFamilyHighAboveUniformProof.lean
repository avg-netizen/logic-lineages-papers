module
public import LogicLineages.PermittedControl.ActualNamedBitFamilyHighAboveTargets
import LogicLineages.PermittedControl.ActualBitFamilyHighRankProof
import LogicLineages.PermittedControl.ActualNamedBitFamilyHighAboveSetupProof
import LogicLineages.PermittedControl.ActualNamedBitFamilyHighSetupProof
import LogicLineages.PermittedControl.ActualBitFamilyHighUniformProof
import LogicLineages.PermittedControl.OriginalRankedLiteralClauseHighPointProof
import LogicLineages.PermittedControl.ActualGreatestRouteResidualProof
import LogicLineages.PermittedControl.ActualSymbolicPredecessorProjectionProof
import LogicLineages.PermittedControl.ActualGuardedResidualBitFamilyProof
import LogicLineages.PermittedControl.ActualLowerRankChartRowsProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualNamedBitFamilyHighAbove
open OrdinalComparison
open ActualGuardedResidualBitFamily (Family Holds exactGuardedResidualUnion)
open ActualBitFamilyLowSlices (coordinates)
open ActualFiniteOrderBranches (Pattern rename)
open ActualRankChartPrototype (readWithin seed)
open ActualLowerRankChartRows (LowerChartCondition exactLowerRankChartRows lowerChart)
open OriginalPrintedPlainMatrixLinearProjection (top)
open OriginalRankedLiteralClauseHigh (highPackets rankedPredecessor highPacketShape exactRankedLiteralHigh)
open ActualSymbolicPredecessorProjection (prepend exactSymbolicPredecessorAppend exactSymbolicPredecessorProjection)
open ActualSelectedSignedRoutePacket (Shape)
open ActualSelectedSignedRouteProjection (project LowerHolds)
open ActualGreatestRouteResidual (Residual rows exactActualLowerRouteFamily)
open ActualPreparedSlotAppend (Packet)
open ActualBoundedSignedRoutes (PacketHolds)
open OriginalMatrixLowDimension (supportSet)
open OriginalPrintedHighResidual (guardedRows)

open ActualBitFamilyHigh (ranked AllPaid exactGenericRankTransport amendedShapes)
open ActualNamedBitFamilyHigh (Supplied Valid renameIndex)

private theorem rankReads (family : Family) (names : List Nat) (p : Pattern)
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

private theorem residualPacket (f lower : Nat → Nat) (C : Nat) (family : Family) (p : Pattern) :
    (∃ out ∈ outputs C family p, ActualGreatestRouteResidual.LowerMatrix f lower out) ↔
      ∃ z : Nat, seed C p lower ≤ z ∧
        ∃ q ∈ highPackets p.1 (top p) (ranked p family), PacketHolds f lower (top p) z q := by
  let qs := highPackets p.1 (top p) (ranked p family)
  let greatest := top p
  let compiled := qs.map (prepend greatest)
  have reduction := (exactActualLowerRouteFamily f lower greatest C compiled (amendedShapes p family)).2
  refine reduction.symm.trans ?_
  constructor
  · rintro ⟨output,atOutput,lifted⟩
    obtain ⟨q,used,rfl⟩ := List.mem_map.mp atOutput
    have shape := highPacketShape p.1 greatest (ranked p family) q used
    obtain ⟨z,high,passes⟩ := (exactSymbolicPredecessorProjection f lower greatest C q shape).mp lifted
    exact ⟨z,high,q,used,passes⟩
  · rintro ⟨z,high,q,used,passes⟩
    have shape := highPacketShape p.1 greatest (ranked p family) q used
    exact ⟨prepend greatest q,List.mem_map.mpr ⟨q,used,rfl⟩,
      (exactSymbolicPredecessorProjection f lower greatest C q shape).mpr ⟨z,high,passes⟩⟩

theorem exactAboveUniformChartChild : ExactAboveUniformChartChild := by
  intro f B C chosen family names support large p good lower outside
  let greatest := top p
  have chart := (exactLowerRankChartRows f lower C greatest).1
  have decode := (exactGuardedResidualUnion f lower C greatest (outputs C family p)).2
  have source (funded : LowerChartCondition C greatest lower) (z : Nat) (within : seed C p lower ≤ z) :
      (∃ q ∈ highPackets p.1 greatest (ranked p family), PacketHolds f lower greatest z q) ↔
      Holds f (readWithin names p lower outside z) family := by
    have setup := exactAboveHighSetup B C family names large p support good lower funded
    have same (k : Nat) (used : k ∈ coordinates family) :
        Function.update lower greatest z (rename p k) = readWithin names p lower outside z k := by
      have named : k ∈ names := (support.2 k).mpr used
      rw [readWithin,if_pos named]
    exact (exactRankedLiteralHigh f B chosen p.1 greatest lower (ranked p family)
      setup.1 z (setup.2 z within)).symm.trans
        (exactGenericRankTransport f (readWithin names p lower outside z)
          (Function.update lower greatest z) family p same).symm
  constructor
  · intro hold
    obtain ⟨out,inOut,lowerGuard,lowerData⟩ := decode.mp hold
    have ready := chart.mp lowerGuard
    obtain ⟨z,high,q,used,passes⟩ := (residualPacket f lower C family p).mp ⟨out,inOut,lowerData⟩
    exact ⟨ready,z,high,rankReads family names p support good C lower outside ready z high,
      (source ready z high).mp ⟨q,used,passes⟩⟩
  · rintro ⟨ready,z,high,_,actual⟩
    obtain ⟨out,member,lowers⟩ := (residualPacket f lower C family p).mpr ⟨z,high,(source ready z high).mpr actual⟩
    exact decode.mpr ⟨out,member,chart.mpr ready,lowers⟩

end LogicLineages.PermittedControl.ActualNamedBitFamilyHighAbove
