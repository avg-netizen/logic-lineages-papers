module
public import LogicLineages.PermittedControl.ActualZeroClassRecombinedRowTargets
import LogicLineages.PermittedControl.ActualZeroClassRecombinedRowPartitionProof
import LogicLineages.PermittedControl.ActualZeroClassReplacementStatementChecks
import LogicLineages.PermittedControl.ActualZeroClassCohortTransferStatementChecks

@[expose] public section
namespace LogicLineages.PermittedControl.ActualZeroClassRecombinedRow
open OrdinalComparison FieldComparison PreparedProjection MixedSameRankResidue
open ActualZeroClassReplacement ActualZeroClassCohortTransfer

theorem exactRecombinedZeroClassRow : ExactRecombinedZeroClassRow := by
  intro f B selected ρ ordered z C c terms values annotations aligned ready raw member largest dominates zero
  dsimp only
  intro paid
  let ps := cohort f C terms annotations
  let out := replaceRow f C terms values annotations
  let outside := outsideCohort f C terms values annotations
  have original := (StatementChecks.fixed_actualZeroClassReplacement f B selected ρ z C c
    terms values annotations aligned ready raw member largest dominates zero).2
  obtain ⟨_,_,outsideReads,partition⟩ :=
    exactResidualPartition f B selected ρ C terms values annotations aligned ready
  change c + actualSum terms values = (c + out.2) + readSum out.1 at original
  change liftedReads f ρ outside at outsideReads
  change readSum outside + readSum (ps.map SurvivingPrefix.asRead) = readSum out.1 at partition
  have finalRow (moved : List Read) (movedReads : liftedReads f ρ moved)
      (preserved : readSum (ps.map SurvivingPrefix.asRead) = readSum moved) :
      liftedReads f ρ (outside ++ moved) ∧
        c + actualSum terms values = (c + out.2) + readSum (outside ++ moved) := by
    refine ⟨appendLiftedReads f ρ outside moved outsideReads movedReads,?_⟩
    rw [appendReadSum,← preserved,partition]
    exact original
  change ∃ moved : List Read,
    (match leastPrefix ps with
    | none => ps = [] ∧ moved = []
    | some anchor => anchor ∈ ps ∧ (∀ p ∈ ps, anchor.rank ≤ p.rank) ∧
      MovedPrefixes f ρ anchor ps moved ∧ ∀ r ∈ moved, r.1.2.rank = anchor.rank) ∧
    liftedReads f ρ (outside ++ moved) ∧
    c + actualSum terms values = (c + out.2) + readSum (outside ++ moved)
  cases found : leastPrefix ps with
  | none =>
      have noPrefix := (StatementChecks.fixed_actualZeroClassLeastPrefix.1 ps).mp found
      have emptyValue : readSum (ps.map SurvivingPrefix.asRead) = readSum [] := by
        rw [noPrefix,List.map_nil]
      exact ⟨[],⟨noPrefix,rfl⟩,finalRow [] True.intro emptyValue⟩
  | some anchor =>
      have transfer := StatementChecks.fixed_actualZeroClassCohortTransfer
        f B selected ρ ordered C terms values annotations aligned paid
      have chosen : leastPrefix (cohort f C terms annotations) = some anchor := found
      simp only [chosen] at transfer
      obtain ⟨among,minimum,moved,moves,reads,preserved,atRank⟩ := transfer
      exact ⟨moved,⟨among,minimum,moves,atRank⟩,finalRow moved reads preserved⟩

end LogicLineages.PermittedControl.ActualZeroClassRecombinedRow
