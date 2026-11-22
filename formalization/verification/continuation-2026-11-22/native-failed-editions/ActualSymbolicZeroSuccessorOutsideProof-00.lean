module
public import LogicLineages.PermittedControl.ActualSymbolicZeroSuccessorTargets
import LogicLineages.PermittedControl.ActualZeroSuccessorPrefixPlanCountProof
import LogicLineages.PermittedControl.SelectedCountOnlyClassProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualSymbolicZeroSuccessor
open OrdinalComparison FieldComparison PreparedProjection
open MixedSameRankResidue (WeightedOperand)
open ActualZeroSuccessorMarkedClass (actualMarked selected)
open ActualZeroSuccessorPrefixPlan (countPlan exactCountPrefixPlan)
open ActualMixedRowLeadingAnnotations (Annotation ActualAnnotation CountTailReady fullValue)
open ActualZeroClassCohortTransfer (survivingPrefix)
open ActualZeroClassReplacement (Read replaceOccurrence replaceRow)
open ActualZeroClassRecombinedRow (outsideCohort)
open SelectedCountOnlyClass (prefixTarget prefixNotationExact)

private noncomputable def residualHead (f : Nat → Nat) (C : Nat)
    (t : WeightedOperand) (v : Nat) (a : Annotation) : List Read :=
  match survivingPrefix f C t a with
  | none => (replaceOccurrence f C t v a).1.toList
  | some _ => []

private theorem headPlan (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (θ : Nat → Nat) (C : Nat) (t : WeightedOperand) (v : Nat) (a : Annotation)
    (actual : LowerOperandActual f θ t.2 v) (ann : ActualAnnotation f θ t v a)
    (ready : t.1 ≠ 0 → CountTailReady θ t.2) :
    (if kept (t,selected f C a) then [t] else []) = (residualHead f C t v a).map Prod.fst ∧
    originShift (t,selected f C a) = some (replaceOccurrence f C t v a).2 := by
  cases a with
  | zeroWeight =>
      have zero : t.1 = 0 := ann
      simp [kept,selected,fullValue,residualHead,survivingPrefix,replaceOccurrence,originShift,zero]
  | linear =>
      have nz : t.1 ≠ 0 := ann.1
      simp [kept,selected,fullValue,residualHead,survivingPrefix,replaceOccurrence,originShift,nz]
  | ordinary q =>
      obtain ⟨nz,rank,F,op,_⟩ := ann
      by_cases same : f q = C <;>
        simp [kept,selected,fullValue,residualHead,survivingPrefix,replaceOccurrence,originShift,nz,op,same]
  | count i q κ =>
      obtain ⟨nz,rank,lam,mu,op,ann⟩ := ann
      by_cases same : f q = C
      · have funded : CountTailReady θ (.count rank lam mu) := by simpa only [op] using ready nz
        have real : LowerOperandActual f θ (.count rank lam mu) v := by simpa only [op] using actual
        obtain ⟨_,first,_,_,_,κEq,_⟩ := ann
        have original : FirstEntry f (countInitial lam.1.repr (θ rank)) (prefixTarget mu).1.repr i := by
          rw [prefixNotationExact.2 mu]
          exact first
        have planFacts := exactCountPrefixPlan f B hf θ rank lam mu v i funded.1 funded.2 real original
        cases plan : countPlan lam mu with
        | invalid => rw [plan] at planFacts; exact False.elim planFacts
        | identity =>
            rw [plan] at planFacts
            have iz : i = 0 := planFacts.1
            simp [kept,selected,fullValue,residualHead,survivingPrefix,replaceOccurrence,
              originShift,nz,op,same,plan,iz,κEq]
        | short eta k =>
            rw [plan] at planFacts
            have gap : shortGapLength lam (prefixTarget mu) = k := planFacts.2.1
            have kNZ : k ≠ 0 := Nat.ne_of_gt planFacts.2.2.1
            have iNZ : i ≠ 0 := Nat.ne_of_gt planFacts.2.2.2.1.1
            simp [kept,selected,fullValue,residualHead,survivingPrefix,replaceOccurrence,
              originShift,nz,op,same,plan,iNZ,gap,kNZ,κEq]
        | survives eta =>
            rw [plan] at planFacts
            have gap : shortGapLength lam (prefixTarget mu) = 0 := planFacts.2.1
            have iNZ : i ≠ 0 := Nat.ne_of_gt planFacts.2.2.1
            simp [kept,selected,fullValue,residualHead,survivingPrefix,replaceOccurrence,
              originShift,nz,op,same,plan,iNZ,gap,κEq]
      · simp [kept,selected,fullValue,residualHead,survivingPrefix,replaceOccurrence,originShift,
          nz,op,same]

theorem exactOutsideAndOriginShiftSyntax : ExactOutsideAndOriginShiftSyntax := by
  intro f B hf θ C terms values anns aligned ready
  induction aligned with
  | nil => exact ⟨rfl,rfl⟩
  | @cons t terms v values a anns actual enc ann tail ih =>
      let head := (t,selected f C a)
      let rest := actualMarked f C terms anns
      have details := headPlan f B hf θ C t v a actual ann (ready t List.mem_cons_self)
      have restDetails := ih (fun u hu => ready u (List.mem_cons_of_mem _ hu))
      constructor
      · change outsideSyntax (head::rest) =
          (residualHead f C t v a ++ outsideCohort f C terms values anns).map Prod.fst
        rw [List.map_append,← details.1,← restDetails.1]
        cases h : kept head <;> simp [outsideSyntax,h,head]
      · change originShifts (head::rest) = some ((replaceOccurrence f C t v a).2 +
            (replaceRow f C terms values anns).2)
        simp [originShifts,show originShift head = _ from details.2,
          show originShifts rest = _ from restDetails.2]

end LogicLineages.PermittedControl.ActualSymbolicZeroSuccessor
