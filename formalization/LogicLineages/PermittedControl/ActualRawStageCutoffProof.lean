module
public import LogicLineages.PermittedControl.ActualRawStageCutoffTargets
import LogicLineages.PermittedControl.ActualBitFamilyRawLayoutProof
import LogicLineages.PermittedControl.ActualBitFamilyRawChartsProof
import LogicLineages.PermittedControl.ActualBitFamilyRawRankProof
import LogicLineages.PermittedControl.ActualRawMixedFamilyCeilingProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualRawStageCutoff
open ActualBitFamilyRawLayout (names encodeFamily exactRawFamilyNames)
open ActualBitFamilyRawCharts (nonemptyPatterns exactNonemptyPatterns)
open ActualGuardedResidualBitFamily (Family)
open ActualFiniteOrderBranches (Pattern patterns)
open ActualNamedBitFamilyHigh (Supplied cutoff)
open ActualBitFamilyHigh (ranked)
open OriginalRankedLiteralClauseHigh (familyNeed)
open ActualRawMixedFamilyCeiling (exactFamilyBound)
open ActualBitFamilyRawRank (exactRawRankCalibration)

theorem chartTapeLiteral (source : List Nat) (uniq : source.Nodup) :
    nonemptyPatterns source = ActualNamedBitFamilyHigh.charts source := by
  unfold nonemptyPatterns ActualNamedBitFamilyHigh.charts
  apply List.filter_congr
  intro p listed
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · intro pos
    have inRaw : p ∈ nonemptyPatterns source := List.mem_filter.mpr ⟨listed,decide_eq_true pos⟩
    exact ⟨pos,((exactNonemptyPatterns source uniq p).mp inRaw).2.2⟩
  · exact And.left

private theorem familySource (family : Family) : Supplied family (names (encodeFamily family)) := by
  have uniq := (exactRawFamilyNames.1 (encodeFamily family)).2.1
  have supportEq := (exactRawFamilyNames.2 family).1
  refine ⟨uniq,?_⟩
  intro k
  rw [← supportEq,List.mem_toFinset]

theorem exactRawStageNamesAndCharts : ExactRawStageNamesAndCharts := by
  refine ⟨chartTapeLiteral,?_⟩
  intro family
  have source := familySource family
  exact ⟨source,chartTapeLiteral _ source.1⟩

theorem chartCostMajorant (B : Nat) (family : Family) (p : Pattern) :
    familyNeed B p.1 (ranked p family) ≤ chartCost B (encodeFamily family) p := by
  unfold chartCost
  rw [exactRawRankCalibration]
  exact exactFamilyBound B p.1 (ranked p family)

private theorem memCost {α : Type} (cost : α → Nat) (xs : List α) (x : α) (used : x ∈ xs) :
    cost x ≤ xs.foldr (fun a n => max (cost a) n) 0 := by
  induction xs with
  | nil => cases used
  | cons a tail ih =>
      change cost x ≤ max (cost a) (tail.foldr (fun i n => max (cost i) n) 0)
      rcases List.mem_cons.mp used with first | rest
      · subst x
        exact le_max_left _ _
      · exact (ih rest).trans (le_max_right _ _)

theorem exactRawRankedChartCost : ExactRawRankedChartCost := by
  refine ⟨chartCostMajorant,?_⟩
  intro B family p used
  have eq := (exactRawStageNamesAndCharts.2 family).2
  rw [← eq] at used
  exact (chartCostMajorant B family p).trans
    (memCost (chartCost B (encodeFamily family)) _ p used)

private theorem foldCostsLe {α : Type} (a b : α → Nat) (xs : List α)
    (wise : ∀ x : α, a x ≤ b x) :
    xs.foldr (fun x n => max (a x) n) 0 ≤ xs.foldr (fun x n => max (b x) n) 0 := by
  induction xs with
  | nil => exact Nat.le_refl _
  | cons x xs ih => exact max_le_max (wise x) ih

theorem exactRawStageCutoffMajorant : ExactRawStageCutoffMajorant := by
  intro B family
  unfold cutoff stageBound
  rw [(exactRawStageNamesAndCharts.2 family).2]
  exact foldCostsLe _ _ _ (chartCostMajorant B family)

end LogicLineages.PermittedControl.ActualRawStageCutoff
