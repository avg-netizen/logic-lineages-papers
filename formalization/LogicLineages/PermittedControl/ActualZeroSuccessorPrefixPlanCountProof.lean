module
public import LogicLineages.PermittedControl.ActualZeroSuccessorPrefixPlanTargets
import LogicLineages.PermittedControl.ActualCountCoreLabelsLongProof
import LogicLineages.PermittedControl.ActualZeroClassReplacementPrefixProof
import LogicLineages.PermittedControl.EntryLinearProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualZeroSuccessorPrefixPlan
open OrdinalComparison FieldComparison PreparedProjection
open SelectedCountOnlyClass (prefixTarget)
open ActualZeroClassReplacement (exactPrefixRead exactShortPrefix)

theorem exactCountPrefixPlan : ExactCountPrefixPlan := by
  intro f B selected ρ rank lam mu v i long tail original current
  let eta := prefixTarget mu
  let A := countInitial lam.1.repr (ρ rank)
  obtain ⟨F,j,k,q,_,properPlan,identityPlan,below,actualFirst,_⟩ :=
    ActualCountCoreLabels.exactPaidLongCountCoreLabel f B selected ρ rank lam mu long tail
  have same := firstEntry_unique f A eta.1.repr i j current actualFirst
  have originalPrefix := exactPrefixRead f ρ rank lam mu v i original below current
  rcases below.eq_or_lt with eq | lt
  · obtain ⟨tag,_,jZero⟩ := identityPlan eq
    have zero : i = 0 := same.trans jZero
    rw [countPlan,tag]
    exact ⟨zero,eq⟩
  · obtain ⟨tag,_,jPos⟩ := properPlan lt
    have pos : 0 < i := same.symm ▸ jPos
    have nz : i ≠ 0 := Nat.ne_of_gt pos
    obtain ⟨lit,hit⟩ := originalPrefix.2 nz
    have exactRead : strictPrefixRead f ρ rank lam eta i := ⟨pos,lit,hit⟩
    rw [countPlan,tag]
    change PlanFacts f B ρ rank lam mu i
      (if shortGapLength lam (prefixTarget mu) = 0 then .survives (prefixTarget mu)
        else .short (prefixTarget mu) (shortGapLength lam (prefixTarget mu)))
    by_cases gap : shortGapLength lam eta = 0
    · have real : shortGapLength lam (prefixTarget mu) = 0 := gap
      rw [if_pos real]
      exact ⟨rfl,real,exactRead⟩
    · have real : shortGapLength lam (prefixTarget mu) ≠ 0 := gap
      rw [if_neg real]
      have kPos := Nat.pos_of_ne_zero gap
      exact ⟨rfl,rfl,kPos,exactRead,fun paid =>
        exactShortPrefix f B selected ρ rank lam eta i lit kPos paid⟩

end LogicLineages.PermittedControl.ActualZeroSuccessorPrefixPlan
