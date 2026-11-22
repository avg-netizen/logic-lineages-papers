module
public import LogicLineages.PermittedControl.ActualBitFamilyHighTargets
import LogicLineages.PermittedControl.ActualBitFamilyHighRankProof
import LogicLineages.PermittedControl.ActualBitFamilyHighUniformProof
import LogicLineages.PermittedControl.ActualFiniteOrderBranchesCoverageProof
import LogicLineages.PermittedControl.ActualFiniteOrderBranchesEnumerateProof
import LogicLineages.PermittedControl.ActualFiniteOrderBranchesRealizationProof
import LogicLineages.PermittedControl.ActualRankChartPrototypeReadProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualBitFamilyHigh
open ActualGuardedResidualBitFamily (Family Holds)
open ActualBitFamilyLowSlices (coordinates dimension)
open ActualFiniteOrderBranches (Pattern actualPattern guard realized rename exactActualBranchCoverage
  exactPatternEnumeration exactBranchRealization)
open ActualRankChartPrototype (Consistent exactChartConsistency seed readWithin)
open ActualLowerRankChartRows (LowerChartCondition)
open OriginalRankedLiteralClauseHigh (rankedPredecessor)
open OriginalPrintedPlainMatrixLinearProjection (top)

private theorem actualChartValues (family : Family) (p : Pattern) (member : p ∈ ActualFiniteOrderBranches.patterns (names family))
    (θ : Nat → Nat) (checked : (guard p).eval θ) (nonempty : 0 < dimension family)
    (C : Nat) (paid : AllPaid C family θ) :
    0 < p.1 ∧ LowerChartCondition C (top p) (realized θ p) ∧
      seed C p (realized θ p) ≤ realized θ p (top p) ∧
      readWithin (names family) p (realized θ p) θ (realized θ p (top p)) = θ := by
  let greatest := top p
  let names := ActualBitFamilyHigh.names family
  let base := realized θ p
  obtain ⟨_,keys,bounds,onto⟩ := (exactPatternEnumeration names p).mp member
  obtain ⟨strict,slots,ties⟩ := exactBranchRealization θ names p member checked
  have width : 0 < p.1 := by
    obtain ⟨n,used⟩ := Finset.card_pos.mp nonempty
    have input : n ∈ names := Finset.mem_toList.mpr used
    exact (Nat.zero_le _).trans_lt (ties n input).1
  have payRank (i : Nat) (used : i < p.1) : C ≤ base i := by
    obtain ⟨e,member,eq⟩ := onto i used
    have n : e.1 ∈ names := by
      rw [← keys]
      exact List.mem_map.mpr ⟨e,member,rfl⟩
    change C ≤ realized θ p i
    rw [← eq,(slots e member).2]
    exact paid e.1 (Finset.mem_toList.mp n)
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

theorem exactGenericHighExistential : ExactGenericHighExistential := by
  intro f B chosen family nonempty
  let C := cutoff B family
  constructor
  · rintro ⟨θ,paid,truth⟩
    let p := actualPattern θ (names family)
    obtain ⟨member,checked⟩ := exactActualBranchCoverage θ (names family)
    obtain ⟨width,lower,high,actual⟩ := actualChartValues family p member θ checked nonempty C paid
    have good : ValidChart family p := ⟨member,width,exactChartConsistency θ p checked⟩
    let base := realized θ p
    have rawTruth : Holds f (readWithin (names family) p base θ (base (top p))) family := by
      rw [actual]
      exact truth
    have rawPaid : AllPaid C family (readWithin (names family) p base θ (base (top p))) := by
      rw [actual]
      exact paid
    have childTruth := (exactGenericUniformChartChild f B chosen family p good base θ).mpr
      ⟨lower,base (top p),high,rawPaid,rawTruth⟩
    exact ⟨(p,child B family p),List.mem_map.mpr ⟨p,(exactValidGenericCharts family p).mpr good,rfl⟩,base,childTruth⟩
  · rintro ⟨result,member,lower,truth⟩
    obtain ⟨p,listed,rfl⟩ := List.mem_map.mp member
    have good := (exactValidGenericCharts family p).mp listed
    obtain ⟨_,z,_,paid,source⟩ :=
      (exactGenericUniformChartChild f B chosen family p good lower (fun _ => 0)).mp truth
    exact ⟨readWithin (names family) p lower (fun _ => 0) z,paid,source⟩

end LogicLineages.PermittedControl.ActualBitFamilyHigh
