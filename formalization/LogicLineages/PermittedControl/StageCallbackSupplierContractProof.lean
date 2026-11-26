module
public import LogicLineages.PermittedControl.StageCallbackSupplierTargets
import LogicLineages.PermittedControl.StageCallbackSupplierPointProof
import LogicLineages.PermittedControl.StageCallbackSupplierChartProof
import LogicLineages.PermittedControl.ActualNamedBitFamilyHighSetupProof
import LogicLineages.PermittedControl.ActualFiniteOrderBranchesCoverageProof
import LogicLineages.PermittedControl.ActualFiniteOrderBranchesEnumerateProof
import LogicLineages.PermittedControl.ActualFiniteOrderBranchesRealizationProof
import LogicLineages.PermittedControl.ActualRankChartPrototypeReadProof
import LogicLineages.PermittedControl.ActualGreatestRouteResidualProof
import LogicLineages.PermittedControl.ActualBitFamilyLowSlicesProof
import LogicLineages.PermittedControl.ActualGuardedResidualBitFamilyProof
import LogicLineages.PermittedControl.ActualLowerRankChartRowsProof
import LogicLineages.PermittedControl.ActualRawStageCutoffProof
import LogicLineages.PermittedControl.ActualBitFamilyRawRankProof

@[expose] public section
namespace LogicLineages.PermittedControl.StageCallbackSupplier
open ActualGuardedResidualBitFamily (Family Holds exactGuardedResidualUnion)
open ActualBitFamilyLowSlices (coordinates coordinateClause originalRows dimension)
open ActualFiniteOrderBranches (Pattern actualPattern guard realized rename
  exactActualBranchCoverage exactPatternEnumeration exactBranchRealization)
open ActualRankChartPrototype (Consistent exactChartConsistency seed readWithin)
open ActualLowerRankChartRows (LowerChartCondition lowerChart exactLowerRankChartRows)
open OriginalRankedLiteralClauseHigh (rankedPredecessor)
open OriginalPrintedPlainMatrixLinearProjection (top)
open OriginalPrintedHighResidual (guardedRows)
open ActualGreatestRouteResidual (Residual rows exactActualLowerRouteFamily)
open ActualSymbolicPredecessorProjection (prepend)
open OriginalMatrixLowDimension (supportSet)
open ActualBitFamilyHigh (ranked AllPaid)
open ActualNamedBitFamilyHigh (Valid Supplied charts exactNamedCharts checkedLength)
open ActualBitFamilyRawLayout (encodeFamily)
open ActualRawMixedFamilyCeiling (familyBound)
open ActualRawStageCutoff (stageBound chartCost exactRawStageNamesAndCharts)
open ActualBitFamilyRawRank (exactRawRankCalibration)
open ActualBitFamilyRawDriver (HighProgram)
open ActualBitFamilyExistentialLow (Satisfiable)
open OriginalPrintedRawStageQuery (HighAtStage)

/-- An all-paid valuation determines its own valid chart, lower table and
greatest value; reading the chart back returns the valuation itself. -/
theorem actualChartValues (family : Family) (names : List Nat) (supports : Supplied family names)
    (p : Pattern) (member : p ∈ ActualFiniteOrderBranches.patterns names)
    (θ : Nat → Nat) (checked : (guard p).eval θ) (nonempty : 0 < dimension family)
    (C : Nat) (paid : AllPaid C family θ) :
    0 < p.1 ∧ LowerChartCondition C (top p) (realized θ p) ∧
      seed C p (realized θ p) ≤ realized θ p (top p) ∧
      readWithin names p (realized θ p) θ (realized θ p (top p)) = θ := by
  let greatest := top p
  let base := realized θ p
  obtain ⟨_,keys,bounds,onto⟩ := (exactPatternEnumeration names p).mp member
  obtain ⟨strict,slots,ties⟩ := exactBranchRealization θ names p member checked
  have width : 0 < p.1 := by
    obtain ⟨n,used⟩ := Finset.card_pos.mp nonempty
    have input : n ∈ names := (supports.2 n).mpr used
    exact (Nat.zero_le _).trans_lt (ties n input).1
  have payRank (i : Nat) (used : i < p.1) : C ≤ base i := by
    obtain ⟨e,member,eq⟩ := onto i used
    have n : e.1 ∈ names := by
      rw [← keys]
      exact List.mem_map.mpr ⟨e,member,rfl⟩
    change C ≤ realized θ p i
    rw [← eq,(slots e member).2]
    exact paid e.1 ((supports.2 e.1).mp n)
  have topWidth : greatest < p.1 := by
    change p.1-1 < p.1
    omega
  have chart : LowerChartCondition C greatest base :=
    ⟨fun i h => payRank i (h.trans topWidth),fun i j lt _ => strict lt⟩
  have pred : rankedPredecessor greatest base ≤ base greatest := by
    by_cases zero : greatest = 0
    · simp only [rankedPredecessor,if_pos zero,Nat.zero_le]
    · rw [rankedPredecessor,if_neg zero]
      exact Nat.succ_le_of_lt (strict (show greatest-1 < greatest by omega))
  refine ⟨width,chart,max_le (payRank greatest topWidth) pred,?_⟩
  funext n
  by_cases used : n ∈ names
  · change readWithin names p base θ (base greatest) n = θ n
    rw [readWithin,if_pos used]
    change Function.update base greatest (base greatest) (rename p n) = θ n
    rw [Function.update_eq_self]
    exact (ties n used).2
  · change readWithin names p base θ (base greatest) n = θ n
    rw [readWithin,if_neg used]

theorem exactSuppliedHighExistential : ExactSuppliedHighExistential := by
  intro f B C alt shaped rowwise family names supplied paidRaw nonempty
  constructor
  · rintro ⟨θ,paid,truth⟩
    let p := actualPattern θ names
    obtain ⟨member,checked⟩ := exactActualBranchCoverage θ names
    obtain ⟨width,lower,high,actual⟩ :=
      actualChartValues family names supplied p member θ checked nonempty C paid
    have good : Valid names p := ⟨member,width,exactChartConsistency θ p checked⟩
    let base := realized θ p
    have rawTruth : Holds f (readWithin names p base θ (base (top p))) family := by
      rw [actual]
      exact truth
    have rawPaid : AllPaid C family (readWithin names p base θ (base (top p))) := by
      rw [actual]
      exact paid
    have childTruth := (exactSuppliedUniformChartChild f B C alt shaped rowwise family names
      supplied paidRaw p good base θ).mpr ⟨lower,base (top p),high,rawPaid,rawTruth⟩
    exact ⟨(p,child alt C family p),
      List.mem_map.mpr ⟨p,(exactNamedCharts names p).mpr good,rfl⟩,base,childTruth⟩
  · rintro ⟨result,member,lower,truth⟩
    obtain ⟨p,listed,rfl⟩ := List.mem_map.mp member
    have good := (exactNamedCharts names p).mp listed
    obtain ⟨_,z,_,paid,source⟩ :=
      (exactSuppliedUniformChartChild f B C alt shaped rowwise family names supplied paidRaw
        p good lower (fun _ => 0)).mp truth
    exact ⟨readWithin names p lower (fun _ => 0) z,paid,source⟩

theorem guardedBelow (C greatest : Nat) (out : Residual)
    (lower : ∀ k ∈ supportSet (rows out), k < greatest) :
    ∀ k ∈ supportSet (guardedRows C greatest out), k < greatest := by
  intro k used
  obtain ⟨r,member,ranked⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp used)
  rcases List.mem_append.mp member with chart | residual
  · obtain ⟨row,atChart,rfl⟩ := List.mem_map.mp chart
    obtain ⟨term,seen,rfl⟩ := List.mem_map.mp ranked
    exact ((exactLowerRankChartRows (fun _ => 0) (fun _ => 0) C greatest).2 row atChart).2 term seen
  · exact lower k (List.mem_toFinset.mpr (List.mem_flatMap.mpr ⟨r,residual,ranked⟩))

theorem exactSuppliedHighDimension : ExactSuppliedHighDimension := by
  intro alt shaped C family names supplied result member
  obtain ⟨p,listed,rfl⟩ := List.mem_map.mp member
  let greatest := top p
  let qs := (packets alt p.1 greatest (ranked p family)).map (prepend greatest)
  let childFamily := child alt C family p
  have good := (exactNamedCharts names p).mp listed
  have width : p.1 ≤ dimension family := by
    have chart := ((exactPatternEnumeration names p).mp good.1).1
    rw [← checkedLength family names supplied]
    exact chart
  have core := (exactActualLowerRouteFamily (fun _ => 0) (fun _ => 0) greatest C qs
    (amendedShapes alt shaped p family)).1
  have source := (exactGuardedResidualUnion (fun _ => 0) (fun _ => 0) C greatest
    (outputs alt C family p)).1
  have scope (k : Nat) (inUnion : k ∈ coordinates childFamily) : k < greatest := by
    obtain ⟨clause,member,atClause⟩ := (coordinateClause childFamily k).mp inUnion
    obtain ⟨out,used,exactOut⟩ := source clause member
    change clause.map Prod.fst = guardedRows C greatest out at exactOut
    change k ∈ supportSet (clause.map Prod.fst) at atClause
    rw [exactOut] at atClause
    exact guardedBelow C greatest out (core out used) k atClause
  have subset : coordinates childFamily ⊆ Finset.range greatest :=
    fun k member => Finset.mem_range.mpr (scope k member)
  have bound : dimension childFamily ≤ greatest := by
    simpa only [Finset.card_range] using Finset.card_le_card subset
  have lower : greatest < p.1 := by
    have pos := good.2.1
    change p.1-1 < p.1
    omega
  exact ⟨scope,bound.trans_lt (lower.trans_le width)⟩

/-- The executable stage bound covers the raw majorant of every valid
chart's ranked family on the encoded family's own name list. -/
theorem stagePaid (B : Nat) (fs : Family) :
    RawPaid B (stageBound B (encodeFamily fs)) fs
      (ActualBitFamilyRawLayout.names (encodeFamily fs)) := by
  intro p listed
  have eq := (exactRawStageNamesAndCharts.2 fs).2
  rw [← eq] at listed
  have cost : chartCost B (encodeFamily fs) p ≤ stageBound B (encodeFamily fs) :=
    foldMaximum (chartCost B (encodeFamily fs)) _ p listed
  have same : chartCost B (encodeFamily fs) p = familyBound B p.1 (encodeFamily (ranked p fs)) := by
    unfold chartCost
    rw [exactRawRankCalibration]
  rw [← same]
  exact cost

theorem exactSuppliedStageCallback : ExactSuppliedStageCallback := by
  intro f B alt shaped rowwise high emits fs nonzero
  have supplied : Supplied fs (ActualBitFamilyRawLayout.names (encodeFamily fs)) :=
    (exactRawStageNamesAndCharts.2 fs).1
  have paid := stagePaid B fs
  refine ⟨emits fs nonzero,?_,?_⟩
  · intro ch member
    obtain ⟨result,listed,rfl⟩ := List.mem_map.mp member
    exact (exactSuppliedHighDimension alt shaped (stageBound B (encodeFamily fs)) fs
      (ActualBitFamilyRawLayout.names (encodeFamily fs)) supplied result listed).2
  · refine (exactSuppliedHighExistential f B (stageBound B (encodeFamily fs)) alt shaped rowwise fs
      (ActualBitFamilyRawLayout.names (encodeFamily fs)) supplied paid nonzero).trans ?_
    constructor
    · rintro ⟨result,listed,lower,truth⟩
      exact ⟨result.2,List.mem_map.mpr ⟨result,listed,rfl⟩,lower,truth⟩
    · rintro ⟨ch,member,lower,truth⟩
      obtain ⟨result,listed,rfl⟩ := List.mem_map.mp member
      exact ⟨result,listed,lower,truth⟩

end LogicLineages.PermittedControl.StageCallbackSupplier
