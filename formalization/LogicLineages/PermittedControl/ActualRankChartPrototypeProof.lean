module
public import LogicLineages.PermittedControl.ActualRankChartPrototypeTargets
import LogicLineages.PermittedControl.ActualRankChartPrototypeReadProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualRankChartPrototype
open OriginalPrintedPlainMatrixInfiniteLow (matrix)
open OriginalPrintedPlainMatrixLinearProjection (top replay)
open OriginalPrintedRankedLiteralHigh (cutoff chartMinimum)
open OriginalMatrixDenseRanks (support)
open OriginalRankedLiteralClauseHigh (rankedPredecessor)
open ActualFiniteOrderBranches (rename realized)

theorem exactOriginalChartPrototype : ExactOriginalChartPrototype := by
  intro B known gates p positive branch used nonempty consistent lower outside chart names C θ
  let greatest := top branch
  obtain ⟨guard,funded,rank⟩ := exactPrototypeChart C names branch used nonempty consistent lower outside chart
  have agree (i : Nat) (below : i < greatest) : realized θ branch i = lower i := by
    refine (rank i below.le).trans ?_
    rw [Function.update_of_ne (ne_of_lt below)]
  have bound :
      rankedPredecessor greatest (realized θ branch) = rankedPredecessor greatest lower := by
    by_cases zero : greatest = 0
    · simp only [rankedPredecessor,if_pos zero]
    · have prev : greatest-1 < greatest := by omega
      simp only [rankedPredecessor,if_neg zero,agree _ prev]
  refine ⟨guard,funded,?_,agree,?_⟩
  · change max C (rankedPredecessor greatest (realized θ branch)) =
      max C (rankedPredecessor greatest lower)
    rw [bound]
  · intro z
    funext name
    by_cases member : name ∈ names
    · by_cases atGreatest : rename branch name = greatest
      · have active : name ∈ support (matrix known gates p) ∧ rename branch name = top branch :=
          ⟨member,atGreatest⟩
        rw [replay,if_pos active,readWithin,if_pos member,atGreatest,Function.update_self]
      · have inactive : ¬ (name ∈ support (matrix known gates p) ∧ rename branch name = top branch) :=
          fun h => atGreatest h.2
        rw [replay,if_neg inactive]
        change readWithin names branch lower outside (seed C branch lower) name = _
        have away : rename branch name ≠ top branch := atGreatest
        simp only [readWithin,if_pos member,Function.update_of_ne away]
    · have inactive : ¬ (name ∈ support (matrix known gates p) ∧ rename branch name = top branch) :=
        fun h => member h.1
      rw [replay,if_neg inactive]
      change readWithin names branch lower outside (seed C branch lower) name = _
      simp only [readWithin,if_neg member]

end LogicLineages.PermittedControl.ActualRankChartPrototype
