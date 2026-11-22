module
public import LogicLineages.PermittedControl.HighTailNamedRowProjectionTargets
import LogicLineages.PermittedControl.HighTailNamedRowProjectionSupportProof
import LogicLineages.PermittedControl.MixedRankNamedResidueRowStatementChecks
import LogicLineages.PermittedControl.MixedRankResidueStatementChecks
import LogicLineages.PermittedControl.RankResidueChoicesStatementChecks
import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsSemanticStatementChecks
import Mathlib.Data.List.Nodup

@[expose] public section
namespace LogicLineages.PermittedControl.HighTailNamedRowProjection
open OrdinalComparison PreparedProjection
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open MixedSameRankResidue (WeightedOperand properOperand orderedReads)
open MixedRankResidue (rankSupport)
open MixedRankNamedResidueRow (row slots)
open SignedRowCoordinateSlice (denotes)
open StatementChecks (fixed_mixedRankNamedResidueRowActual fixed_mixedRankResidueSupport
  fixed_rankResidueLayoutAndChoices)

private theorem slotProjections (terms : List WeightedOperand) :
    ((slots terms).map Prod.fst).Nodup ∧ ((slots terms).map Prod.snd).Nodup := by
  unfold slots
  obtain ⟨ranks,names⟩ := fixed_rankResidueLayoutAndChoices.2.2.1 (rankSupport terms)
  rw [ranks,names]
  exact ⟨List.Nodup.map Nat.succ_injective List.nodup_range,(fixed_mixedRankResidueSupport.1 terms).1⟩

private theorem tieAfterUpdate (terms : List WeightedOperand) (ρ ν : Nat → Nat) (name rank z : Nat)
    (chosen : (name,rank) ∈ slots terms)
    (tied : ∀ s ∈ slots terms, s.1 ≠ name → ν s.1 = ρ s.2) :
    ∀ s ∈ slots terms, Function.update ν name z s.1 = Function.update ρ rank z s.2 := by
  obtain ⟨names,ranks⟩ := slotProjections terms
  intro s member
  by_cases same : s.1 = name
  · have actual : s = (name,rank) := List.inj_on_of_nodup_map names member chosen same
    subst s
    simp
  · have other : s.2 ≠ rank := by
      intro equal
      have actual : s = (name,rank) := List.inj_on_of_nodup_map ranks member chosen equal
      exact same (congrArg Prod.fst actual)
    rw [Function.update_of_ne same,Function.update_of_ne other]
    exact tied s member same

private theorem uniqueValues (f ρ : Nat → Nat) (terms : List WeightedOperand)
    (values others : List Nat) (reads : orderedReads f ρ terms values)
    (again : orderedReads f ρ terms others) : values = others := by
  induction terms generalizing values others with
  | nil => cases values <;> cases others <;> simp [orderedReads] at *
  | cons t ts ih =>
    cases values with
    | nil => exact False.elim reads
    | cons v vs =>
      cases others with
      | nil => exact False.elim again
      | cons w ws =>
        obtain ⟨_,head,tail⟩ := reads
        obtain ⟨_,another,rest⟩ := again
        have same : v = w := Option.some.inj (Option.some.inj (head.symm.trans another))
        exact congrArg₂ List.cons same (ih vs ws tail rest)

private theorem rowAtActual (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (m : Nat) (c : Int) (terms : List WeightedOperand) (ρ ν : Nat → Nat)
    (positive : 0 < m) (proper : ∀ t ∈ terms, properOperand t.2)
    (tails : ∀ r ∈ rankSupport terms, coordinateTail B m terms ≤ ρ r)
    (tied : ∀ s ∈ slots terms, ν s.1 = ρ s.2) :
    (row m c terms).eval ν ↔ denotes f ρ m c terms := by
  obtain ⟨values,reads,meaning⟩ := fixed_mixedRankNamedResidueRowActual
    f B hf m c terms ρ positive proper tails
  refine (meaning ν tied).trans ?_
  constructor
  · intro divisible
    exact ⟨values,reads,divisible⟩
  · rintro ⟨others,again,divisible⟩
    have equal := uniqueValues f ρ terms values others reads again
    subst others
    exact divisible

theorem actualProjection : ActualProjection := by
  intro f B hf m name rank c terms ρ ν positive chosen proper others tied
  have atValue (z : Nat) (high : coordinateTail B m terms ≤ z) :
      (row m c terms).eval (Function.update ν name z) ↔
        denotes f (Function.update ρ rank z) m c terms := by
    apply rowAtActual f B hf m c terms _ _ positive proper
    · intro r used
      by_cases same : r = rank
      · subst r
        simpa using high
      · rw [Function.update_of_ne same]
        exact others r used same
    · exact tieAfterUpdate terms ρ ν name rank z chosen tied
  unfold projected
  rw [LinearRowsSemanticStatementChecks.actual_linear_elimination name _
    (outputSupport B m name c terms).1 ν]
  constructor
  · rintro ⟨z,holds⟩
    change (lowerGuard name (coordinateTail B m terms)).eval (Function.update ν name z) ∧
      (row m c terms).eval (Function.update ν name z) at holds
    rw [lowerGuardEval,Function.update_self] at holds
    exact ⟨z,holds.1,(atValue z holds.1).mp holds.2⟩
  · rintro ⟨z,high,meaning⟩
    refine ⟨z,?_⟩
    change (lowerGuard name (coordinateTail B m terms)).eval (Function.update ν name z) ∧
      (row m c terms).eval (Function.update ν name z)
    rw [lowerGuardEval,Function.update_self]
    exact ⟨high,(atValue z high).mpr meaning⟩

end LogicLineages.PermittedControl.HighTailNamedRowProjection
