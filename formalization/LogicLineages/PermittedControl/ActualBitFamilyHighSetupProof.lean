module
public import LogicLineages.PermittedControl.ActualBitFamilyHighTargets
import LogicLineages.PermittedControl.ActualBitFamilyHighRankProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualBitFamilyHigh
open ActualGuardedResidualBitFamily (Family)
open ActualFiniteOrderBranches (Pattern)
open OriginalPrintedPlainMatrixLinearProjection (top)
open ActualRankChartPrototype (seed)
open OriginalRankedLiteralClauseHigh (OriginalSetup highMinimum familyNeed rankedPredecessor)

private theorem foldMaximum {α : Type} (cost : α → Nat) (xs : List α) (x : α) (h : x ∈ xs) :
    cost x ≤ xs.foldr (fun a n => max (cost a) n) 0 := by
  induction xs with
  | nil => cases h
  | cons a xs ih =>
    rcases List.mem_cons.mp h with same | rest
    · subst a
      exact le_max_left _ _
    · exact (ih rest).trans (le_max_right _ _)

theorem chartCutoff (B : Nat) (family : Family) (p : Pattern) (good : ValidChart family p) :
    familyNeed B p.1 (ranked p family) ≤ cutoff B family := by
  let cost : Pattern → Nat := fun p => familyNeed B p.1 (ranked p family)
  change cost p ≤ (charts family).foldr (fun a n => max (cost a) n) 0
  exact foldMaximum cost (charts family) p ((exactValidGenericCharts family p).mpr good)

theorem exactGenericHighSetup : ExactGenericHighSetup := by
  intro B family p valid lower chart
  have static := chartCutoff B family p valid
  have sourceScope := rankedScope family p valid
  refine ⟨⟨chart.2,?_,?_⟩,?_⟩
  · intro c hc row hr t ht
    have h := sourceScope c hc row hr t ht
    exact ⟨h,by change t.2.rank ≤ p.1-1; omega⟩
  · intro c hc r hr t ht below
    exact static.trans (chart.1 t.2.rank below)
  · intro z high
    change max (familyNeed B p.1 (ranked p family)) (rankedPredecessor (top p) lower) ≤ z
    exact max_le (static.trans ((le_max_left _ _).trans high)) ((le_max_right _ _).trans high)

end LogicLineages.PermittedControl.ActualBitFamilyHigh
