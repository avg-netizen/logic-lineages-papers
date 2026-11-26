module
public import LogicLineages.PermittedControl.SignedCongruenceMatrixTargets
import LogicLineages.PermittedControl.SharedRankResidueRowStatementChecks

@[expose] public section
namespace LogicLineages.PermittedControl.SignedCongruenceMatrix
open OrdinalComparison PreparedProjection
open MixedSameRankResidue (WeightedOperand properOperand orderedReads actualSum)
open MixedRankResidue (rankSupport)
open SharedRankResidueRow (SourceRow Layout commonLayout)
open StatementChecks (fixed_actualSharedRankResidueRow fixed_sharedRankResidueCommonLayout)

private theorem equalOrderedReads (f ρ : Nat → Nat) (terms : List WeightedOperand)
    (first second : List Nat) (left : orderedReads f ρ terms first)
    (right : orderedReads f ρ terms second) : first = second := by
  induction terms generalizing first second with
  | nil => cases first <;> cases second <;> simp [orderedReads] at *
  | cons term terms ih =>
    cases first with
    | nil => exact False.elim left
    | cons v vs =>
      cases second with
      | nil => exact False.elim right
      | cons w ws =>
        obtain ⟨_,vRead,vTail⟩ := left
        obtain ⟨_,wRead,wTail⟩ := right
        have same : v = w := Option.some.inj (Option.some.inj (vRead.symm.trans wRead))
        exact congrArg₂ List.cons same (ih vs ws vTail wTail)

private theorem rowAtLayout (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (layout : Layout) (r : SourceRow) (ρ ν : Nat → Nat)
    (positive : 0 < r.1) (good : ∀ t ∈ r.2.2, properOperand t.2)
    (covered : ∀ rank ∈ rankSupport r.2.2, rank ∈ layout.map Prod.snd)
    (tails : ∀ rank ∈ rankSupport r.2.2, rowTail B r ≤ ρ rank)
    (tied : ∀ s ∈ layout, ν s.1 = ρ s.2) :
    (SharedRankResidueRow.formula layout r).eval ν ↔
      ∃ values : List Nat, orderedReads f ρ r.2.2 values ∧ ((r.1 : Int) ∣ r.2.1 + actualSum r.2.2 values) := by
  obtain ⟨chosen,reads,meaning⟩ :=
    fixed_actualSharedRankResidueRow f B hf layout r ρ positive covered good tails
  refine (meaning ν tied).trans ?_
  constructor
  · intro divisible
    exact ⟨chosen,reads,divisible⟩
  · rintro ⟨values,areReads,divisible⟩
    have same := equalOrderedReads f ρ r.2.2 chosen values reads areReads
    subst values
    exact divisible

private theorem actualAtLayout (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (layout : Layout) (rows : List SourceRow) (ρ ν : Nat → Nat)
    (valid : ∀ r ∈ rows, 0 < r.1 ∧ ∀ t ∈ r.2.2, properOperand t.2)
    (covered : ∀ r ∈ rows, ∀ rank ∈ rankSupport r.2.2, rank ∈ layout.map Prod.snd)
    (tails : ∀ r ∈ rows, ∀ rank ∈ rankSupport r.2.2, rowTail B r ≤ ρ rank)
    (tied : ∀ s ∈ layout, ν s.1 = ρ s.2) :
    (formulaAtLayout layout rows).eval ν ↔ ∃ values : List (List Nat), actualRows f ρ rows values := by
  induction rows with
  | nil =>
    change True ↔ ∃ values : List (List Nat), actualRows f ρ [] values
    exact ⟨fun _ => ⟨[],True.intro⟩,fun _ => True.intro⟩
  | cons r rows ih =>
    have headValid := valid r List.mem_cons_self
    have head := rowAtLayout f B hf layout r ρ ν headValid.1 headValid.2
      (covered r List.mem_cons_self) (tails r List.mem_cons_self) tied
    have tail := ih (fun q member => valid q (List.mem_cons_of_mem _ member))
      (fun q member => covered q (List.mem_cons_of_mem _ member))
      (fun q member => tails q (List.mem_cons_of_mem _ member))
    change ((SharedRankResidueRow.formula layout r).eval ν ∧ (formulaAtLayout layout rows).eval ν) ↔ _
    rw [head,tail]
    constructor
    · rintro ⟨⟨chosen,reads,divides⟩,⟨values,rest⟩⟩
      exact ⟨chosen :: values,⟨reads,divides,rest⟩⟩
    · rintro ⟨allValues,actual⟩
      cases allValues with
      | nil => exact False.elim actual
      | cons chosen values =>
        obtain ⟨reads,divides,rest⟩ := actual
        exact ⟨⟨chosen,reads,divides⟩,⟨values,rest⟩⟩

theorem actualConjunction : ActualConjunction := by
  intro f B hf rows ρ ν valid tails tied
  have layout := fixed_sharedRankResidueCommonLayout rows
  exact actualAtLayout f B hf (commonLayout rows) rows ρ ν valid
    (fun r member rank used => (layout.2.2.2 rank).mpr ⟨r,member,used⟩) tails tied

end LogicLineages.PermittedControl.SignedCongruenceMatrix
