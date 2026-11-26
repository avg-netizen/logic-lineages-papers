module
public import LogicLineages.PermittedControl.ActualNamedBitFamilyHighTargets
import LogicLineages.PermittedControl.ActualNamedBitFamilyHighSetupProof
import LogicLineages.PermittedControl.ActualNamedBitFamilyHighUniformProof
import LogicLineages.PermittedControl.ActualFiniteOrderBranchesCoverageProof
import LogicLineages.PermittedControl.ActualFiniteOrderBranchesEnumerateProof
import LogicLineages.PermittedControl.ActualFiniteOrderBranchesRealizationProof
import LogicLineages.PermittedControl.ActualRankChartPrototypeReadProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualNamedBitFamilyHigh
open ActualGuardedResidualBitFamily (Family Holds)
open ActualBitFamilyLowSlices (coordinates dimension)
open ActualFiniteOrderBranches (Pattern actualPattern guard realized rename exactActualBranchCoverage
  exactPatternEnumeration exactBranchRealization)
open ActualRankChartPrototype (Consistent exactChartConsistency seed readWithin)
open ActualLowerRankChartRows (LowerChartCondition)
open OriginalRankedLiteralClauseHigh (rankedPredecessor)
open OriginalPrintedPlainMatrixLinearProjection (top)

open ActualBitFamilyHigh (AllPaid)

private theorem actualChartValues (family : Family) (names : List Nat) (supports : Supplied family names)
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

theorem exactNamedHighExistential : ExactNamedHighExistential := by
  intro f B chosen family names supplied nonempty
  let C := cutoff B family names
  constructor
  · rintro ⟨θ,paid,truth⟩
    let p := actualPattern θ names
    obtain ⟨member,checked⟩ := exactActualBranchCoverage θ names
    obtain ⟨width,lower,high,actual⟩ := actualChartValues family names supplied p member θ checked nonempty C paid
    have good : Valid names p := ⟨member,width,exactChartConsistency θ p checked⟩
    let base := realized θ p
    have rawTruth : Holds f (readWithin names p base θ (base (top p))) family := by
      rw [actual]
      exact truth
    have rawPaid : AllPaid C family (readWithin names p base θ (base (top p))) := by
      rw [actual]
      exact paid
    have childTruth := (exactNamedUniformChartChild f B chosen family names p supplied good base θ).mpr
      ⟨lower,base (top p),high,rawPaid,rawTruth⟩
    exact ⟨(p,child B family names p),List.mem_map.mpr ⟨p,(exactNamedCharts names p).mpr good,rfl⟩,base,childTruth⟩
  · rintro ⟨result,member,lower,truth⟩
    obtain ⟨p,listed,rfl⟩ := List.mem_map.mp member
    have good := (exactNamedCharts names p).mp listed
    obtain ⟨_,z,_,paid,source⟩ :=
      (exactNamedUniformChartChild f B chosen family names p supplied good lower (fun _ => 0)).mp truth
    exact ⟨readWithin names p lower (fun _ => 0) z,paid,source⟩

end LogicLineages.PermittedControl.ActualNamedBitFamilyHigh
