module
public import LogicLineages.PermittedControl.StageCallbackLegacyTargets
import LogicLineages.PermittedControl.StageCallbackSupplierContractProof
import LogicLineages.PermittedControl.ActualPaidMixedMatrixTuplesRowProof
import LogicLineages.PermittedControl.ActualPaidMixedMatrixTuplesProof
import LogicLineages.PermittedControl.OriginalPrintedLiteralRowBridgeProof
import LogicLineages.PermittedControl.OriginalRankedLiteralClauseHighReadyProof
import LogicLineages.PermittedControl.ActualRawMixedFamilyCeilingProof

@[expose] public section
namespace LogicLineages.PermittedControl.StageCallbackLegacy
open OrdinalComparison
open StageCallbackSupplier (Supplier SupplierShape SupplierExact packets outputs child compile
  stageChildren Emits exactSuppliedStageCallback)
open ActualPaidMixedMatrixTuples (alternatives tuples alternativesShape exactPaidMixedRow
  exactMixedMatrixMinimum)
open ActualSignedRouteCartesian (choices tuplePacket)
open OriginalPrintedTerminalBitClauses (BitRow)
open OriginalPrintedLiteralRowBridge (compileRow properClauses AdmittedLiteralClause
  properClauseMember exactLiteralMixedRowBridge)
open OriginalRankedLiteralClauseHigh (highPackets familyNeed highMinimum OriginalSetup
  exactOriginalLiteralReady)
open ActualGuardedResidualBitFamily (Family reifyFamily)
open ActualFiniteOrderBranches (Pattern)
open ActualBitFamilyHigh (ranked)
open ActualNamedBitFamilyHigh (charts)
open OriginalPrintedPlainMatrixLinearProjection (top)
open ActualSymbolicPredecessorProjection (prepend)
open ActualGreatestRouteResidual (lowerFamily)
open ActualBitFamilyRawLayout (encodeBitRow encodeFamily)
open ActualRawMixedFamilyCeiling (rowBound familyBound exactFamilyBound)

theorem exactLegacySupplierShape : ExactLegacySupplierShape := by
  intro r top row q used
  exact alternativesShape (fun _ => 0) (fun _ => 0) r top 0 (compileRow row) q used

/-- The one-row family's typed need is below that row's raw majorant. -/
theorem singleNeed (B r : Nat) (row : BitRow) :
    familyNeed B r [[row]] ≤ rowBound B r (encodeBitRow row) := by
  have raw : familyBound B r (encodeFamily [[row]]) = rowBound B r (encodeBitRow row) := by
    show max (max (rowBound B r (encodeBitRow row)) 0) 0 = rowBound B r (encodeBitRow row)
    rw [Nat.max_zero,Nat.max_zero]
  exact (exactFamilyBound B r [[row]]).trans (le_of_eq raw)

theorem exactLegacySupplierExact : ExactLegacySupplierExact := by
  intro f B selected r top baseline row z admitted strict scope lower high
  have need := singleNeed B r row
  have setup : OriginalSetup B r top baseline [[row]] := by
    refine ⟨strict,?_,?_⟩
    · intro rows inFamily other inRows t inTerms
      have e1 : rows = [row] := List.mem_singleton.mp inFamily
      rw [e1] at inRows
      have e2 : other = row := List.mem_singleton.mp inRows
      rw [e2] at inTerms
      exact scope t inTerms
    · intro _ _ _ _ t _ below
      exact need.trans (lower t.2.rank below)
  have payment : highMinimum B r top baseline [[row]] ≤ z :=
    max_le (need.trans ((le_max_left _ _).trans high)) ((le_max_right _ _).trans high)
  have clause : AdmittedLiteralClause [row] := by
    intro other inRows
    have e : other = row := List.mem_singleton.mp inRows
    rw [e]
    exact admitted
  have member : [row] ∈ properClauses [[row]] :=
    (properClauseMember [[row]] [row]).mpr ⟨List.mem_singleton.mpr rfl,clause⟩
  have ready := exactOriginalLiteralReady B r top baseline [[row]] setup z payment [row] member
  have here : compileRow row ∈ [row].map compileRow :=
    List.mem_map.mpr ⟨row,List.mem_singleton.mpr rfl,rfl⟩
  have minimum := (exactMixedMatrixMinimum B r top baseline ([row].map compileRow) z).mp
    ready.2.2 (compileRow row) here
  have literal := exactLiteralMixedRowBridge f B selected (Function.update baseline top z) row
    admitted (ready.1 row (List.mem_singleton.mpr rfl))
  have routed := exactPaidMixedRow f B selected r top baseline (compileRow row)
    (ready.2.1 (compileRow row) here) z minimum
  exact literal.trans routed

theorem legacyPackets (r top : Nat) (family : Family) :
    packets legacy r top family = highPackets r top family := by
  have rowsEq (rows : List BitRow) :
      rows.map (legacy r top) = (rows.map compileRow).map (alternatives r top) := by
    induction rows with
    | nil => rfl
    | cons row rest ih => exact congrArg (List.cons (legacy r top row)) ih
  show (properClauses family).flatMap
      (fun rows => (choices (rows.map (legacy r top))).map tuplePacket) =
    (properClauses family).flatMap
      (fun rows => (choices ((rows.map compileRow).map (alternatives r top))).map tuplePacket)
  simp only [rowsEq]

theorem exactLegacyLiteralCompile : ExactLegacyLiteralCompile := by
  refine ⟨legacyPackets,?_⟩
  intro C family names
  have childEq (p : Pattern) :
      child legacy C family p = ActualNamedBitFamilyHighAbove.child C family p := by
    show reifyFamily C (top p) (lowerFamily (top p) C
        ((packets legacy p.1 (top p) (ranked p family)).map (prepend (top p)))) =
      reifyFamily C (top p) (lowerFamily (top p) C
        ((highPackets p.1 (top p) (ranked p family)).map (prepend (top p))))
    rw [legacyPackets]
  show (charts names).map (fun p => (p,child legacy C family p)) =
    (charts names).map (fun p => (p,ActualNamedBitFamilyHighAbove.child C family p))
  simp only [childEq]

theorem exactLegacyStageCallback : ExactLegacyStageCallback := by
  intro f B selected high emits
  exact exactSuppliedStageCallback f B legacy exactLegacySupplierShape
    (exactLegacySupplierExact f B selected) high emits

end LogicLineages.PermittedControl.StageCallbackLegacy
