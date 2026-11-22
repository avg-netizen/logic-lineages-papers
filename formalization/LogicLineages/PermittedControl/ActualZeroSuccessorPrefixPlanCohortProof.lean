module
public import LogicLineages.PermittedControl.ActualZeroSuccessorPrefixPlanTargets
import LogicLineages.PermittedControl.ActualZeroSuccessorPrefixPlanCountProof
import LogicLineages.PermittedControl.SelectedCountOnlyClassProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualZeroSuccessorPrefixPlan
open OrdinalComparison FieldComparison PreparedProjection
open MixedSameRankResidue (WeightedOperand)
open ActualZeroSuccessorMarkedClass (actualMarked selected)
open ActualMixedRowLeadingAnnotations (Annotation ActualAnnotation CountTailReady fullValue)
open ActualZeroClassCohortTransfer (SurvivingPrefix survivingPrefix cohort leastPrefix)
open SelectedCountOnlyClass (prefixTarget prefixNotationExact)

theorem exactCanonicalPrefixAnchor : ExactCanonicalPrefixAnchor := by
  intro ps
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      cases found : leastPrefix ps with
      | none =>
          simp only [found,Option.map_none] at ih
          simp [leastSyntax,leastPrefix,ih,found]
      | some q =>
          simp only [found,Option.map_some] at ih
          by_cases earlier : p.rank ≤ q.rank <;>
            simp [leastSyntax,leastPrefix,ih,found,erase,earlier]

private theorem headProjection (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (ρ : Nat → Nat) (C : Nat) (t : WeightedOperand) (v : Nat) (a : Annotation)
    (actual : LowerOperandActual f ρ t.2 v) (ann : ActualAnnotation f ρ t v a)
    (ready : t.1 ≠ 0 → CountTailReady ρ t.2) :
    markedPrefix (t,selected f C a) = (survivingPrefix f C t a).map erase := by
  cases a with
  | zeroWeight => rfl
  | linear => rfl
  | ordinary q =>
      obtain ⟨_,r,F,op,_⟩ := ann
      by_cases same : f q = C <;>
        simp [markedPrefix,selected,fullValue,same,op,survivingPrefix]
  | count i q κ =>
      obtain ⟨nz,r,lam,mu,op,ann⟩ := ann
      by_cases same : f q = C
      · have paid : CountTailReady ρ (.count r lam mu) := by simpa only [op] using ready nz
        have raw : LowerOperandActual f ρ (.count r lam mu) v := by simpa only [op] using actual
        have first : FirstEntry f (countInitial lam.1.repr (ρ r)) (prefixTarget mu).1.repr i := by
          rw [prefixNotationExact.2 mu]
          exact ann.2.1
        have facts := exactCountPrefixPlan f B hf ρ r lam mu v i paid.1 paid.2 raw first
        cases plan : countPlan lam mu with
        | invalid =>
            rw [plan] at facts
            exact False.elim facts
        | identity =>
            rw [plan] at facts
            have iZero : i = 0 := facts.1
            simp [markedPrefix,selected,fullValue,same,op,plan,survivingPrefix,iZero]
        | short eta k =>
            rw [plan] at facts
            have kNZ : shortGapLength lam (prefixTarget mu) ≠ 0 :=
              facts.2.1.symm ▸ Nat.ne_of_gt facts.2.2.1
            have iNZ : i ≠ 0 := Nat.ne_of_gt facts.2.2.2.1.1
            simp [markedPrefix,selected,fullValue,same,op,plan,survivingPrefix,iNZ,kNZ]
        | survives eta =>
            rw [plan] at facts
            have sameEta : eta = prefixTarget mu := facts.1
            have gap : shortGapLength lam (prefixTarget mu) = 0 := facts.2.1
            have iNZ : i ≠ 0 := Nat.ne_of_gt facts.2.2.1
            simp [markedPrefix,selected,fullValue,same,op,plan,survivingPrefix,iNZ,gap,sameEta,erase]
      · simp [markedPrefix,selected,fullValue,same,op,survivingPrefix]

private theorem cohortProjection (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (ρ : Nat → Nat) (C : Nat) (terms : List WeightedOperand) (values : List Nat)
    (anns : List Annotation)
    (aligned : ActualMixedRowLeadingAnnotations.AlignedAnnotations f ρ terms values anns)
    (ready : ∀ t ∈ terms, t.1 ≠ 0 → CountTailReady ρ t.2) :
    cohortSyntax (actualMarked f C terms anns) = (cohort f C terms anns).map erase := by
  induction aligned with
  | nil => rfl
  | @cons t terms v values a anns actual _ ann _ ih =>
      have head := headProjection f B hf ρ C t v a actual ann (ready t List.mem_cons_self)
      have tail := ih (fun q hq => ready q (List.mem_cons_of_mem _ hq))
      change ((t,selected f C a)::actualMarked f C terms anns).filterMap markedPrefix =
        ((survivingPrefix f C t a).toList ++ cohort f C terms anns).map erase
      rw [List.filterMap_cons,head,List.map_append,← tail]
      cases h : survivingPrefix f C t a <;> rfl

theorem exactSelectedCohortSyntax : ExactSelectedCohortSyntax := by
  intro f B hf ρ C terms values anns aligned ready
  have first := cohortProjection f B hf ρ C terms values anns aligned ready
  refine ⟨first,?_⟩
  rw [first]
  exact exactCanonicalPrefixAnchor _

end LogicLineages.PermittedControl.ActualZeroSuccessorPrefixPlan
