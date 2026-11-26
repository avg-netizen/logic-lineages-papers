module
public import LogicLineages.PermittedControl.StageCallbackSupplierTargets
import LogicLineages.PermittedControl.ActualSignedRouteCartesianChoiceProof
import LogicLineages.PermittedControl.OriginalPrintedLiteralRowBridgeProof
import LogicLineages.PermittedControl.OriginalPrintedLiteralRowBridgeReadProof

@[expose] public section
namespace LogicLineages.PermittedControl.StageCallbackSupplier
open ActualPreparedSlotAppend (Packet)
open ActualSelectedSignedRoutePacket (Shape)
open ActualBoundedSignedRoutes (PacketHolds)
open ActualSignedRouteCartesian (choices tuplePacket exactCartesianPacketEval)
open ActualRankedNormalizationSyntax (LowerStrict)
open OriginalPrintedTerminalBitClauses (BitRow RowHolds ClauseHolds)
open OriginalPrintedLiteralRowBridge (properClauses AdmittedOperandRow AdmittedLiteralClause
  properClauseMember exactLiteralProperClauseFilter)
open OriginalRankedLiteralClauseHigh (rankedPredecessor SourceFamily)
open ActualGuardedResidualBitFamily (Family)
open ActualBitFamilyRawLayout (encodeBitRow encodeFamily)
open ActualRawMixedFamilyCeiling (rowBound clauseBound familyBound)

theorem foldMaximum {α : Type} (cost : α → Nat) (xs : List α) (x : α) (h : x ∈ xs) :
    cost x ≤ xs.foldr (fun a n => max (cost a) n) 0 := by
  induction xs with
  | nil => cases h
  | cons a xs ih =>
    rcases List.mem_cons.mp h with same | rest
    · subst a
      exact le_max_left _ _
    · exact (ih rest).trans (le_max_right _ _)

/-- A row of a clause of the family is covered by the family's raw majorant. -/
theorem rowBelowFamily (B r : Nat) (family : Family) (rows : List BitRow) (member : rows ∈ family)
    (row : BitRow) (used : row ∈ rows) :
    rowBound B r (encodeBitRow row) ≤ familyBound B r (encodeFamily family) := by
  have inner : rowBound B r (encodeBitRow row) ≤ clauseBound B r (rows.map encodeBitRow) :=
    foldMaximum (rowBound B r) (rows.map encodeBitRow) (encodeBitRow row)
      (List.mem_map.mpr ⟨row,used,rfl⟩)
  have outer : clauseBound B r (rows.map encodeBitRow) ≤ familyBound B r (encodeFamily family) :=
    foldMaximum (clauseBound B r) (encodeFamily family) (rows.map encodeBitRow)
      (List.mem_map.mpr ⟨rows,member,rfl⟩)
  exact inner.trans outer

theorem alternativeShapes (alt : Supplier) (shaped : SupplierShape alt) (r top : Nat)
    (rows : List BitRow) : ∀ pack ∈ rows.map (alt r top), ∀ p ∈ pack, Shape p := by
  intro pack inPack p inP
  obtain ⟨row,_,rfl⟩ := List.mem_map.mp inPack
  exact shaped r top row p inP

theorem exactSuppliedPacketShape : ExactSuppliedPacketShape := by
  intro alt shaped r top family q used
  obtain ⟨rows,_,here⟩ := List.mem_flatMap.mp used
  obtain ⟨tuple,member,rfl⟩ := List.mem_map.mp here
  exact (exactCartesianPacketEval (fun _ => 0) (fun _ => 0) top 0 (rows.map (alt r top))
    (alternativeShapes alt shaped r top rows)).1 tuple member

theorem exactSuppliedRankedPoint : ExactSuppliedRankedPoint := by
  intro f B alt shaped rowwise r top baseline family z strict scope lower high
  have rowExact (rows : List BitRow) (member : rows ∈ properClauses family)
      (row : BitRow) (used : row ∈ rows) :
      RowHolds f (Function.update baseline top z) row ↔
        ∃ q ∈ alt r top row, PacketHolds f baseline top z q := by
    obtain ⟨inFamily,admitted⟩ := (properClauseMember family rows).mp member
    have bound := rowBelowFamily B r family rows inFamily row used
    exact rowwise r top baseline row z (admitted row used) strict (scope rows inFamily row used)
      (fun i below => bound.trans (lower i below))
      (max_le (bound.trans ((le_max_left _ _).trans high)) ((le_max_right _ _).trans high))
  refine (exactLiteralProperClauseFilter f (Function.update baseline top z) family).trans ?_
  constructor
  · rintro ⟨rows,member,live⟩
    have cart := (exactCartesianPacketEval f baseline top z (rows.map (alt r top))
      (alternativeShapes alt shaped r top rows)).2
    have each : ∀ pack ∈ rows.map (alt r top), ∃ p ∈ pack, PacketHolds f baseline top z p := by
      intro pack inPack
      obtain ⟨row,used,rfl⟩ := List.mem_map.mp inPack
      exact (rowExact rows member row used).mp (live row used)
    obtain ⟨tuple,chosen,actual⟩ := cart.mpr each
    exact ⟨tuplePacket tuple,
      List.mem_flatMap.mpr ⟨rows,member,List.mem_map.mpr ⟨tuple,chosen,rfl⟩⟩,actual⟩
  · rintro ⟨q,used,actual⟩
    obtain ⟨rows,member,rest⟩ := List.mem_flatMap.mp used
    obtain ⟨tuple,chosen,rfl⟩ := List.mem_map.mp rest
    have cart := (exactCartesianPacketEval f baseline top z (rows.map (alt r top))
      (alternativeShapes alt shaped r top rows)).2
    have all := cart.mp ⟨tuple,chosen,actual⟩
    exact ⟨rows,member,fun row used => (rowExact rows member row used).mpr
      (all (alt r top row) (List.mem_map.mpr ⟨row,used,rfl⟩))⟩

end LogicLineages.PermittedControl.StageCallbackSupplier
