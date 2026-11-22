module
public import LogicLineages.PermittedControl.ActualZeroClassOutsideAndShiftTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualZeroClassOutsideAndShift
open OrdinalComparison FieldComparison PreparedProjection
open ActualMixedRowLeadingAnnotations ActualZeroClassReplacement ActualZeroClassCohortTransfer
open ActualCountOriginDispositions
open SelectedCountOnlyClass (prefixTarget)
open InnerTerminationTargets (Disposition)

theorem initialShiftAtCount (f : Nat → Nat) (ρ : Nat → Nat) (C : Nat) (rd : Read)
    (ann : Annotation) (anchor : Option SurvivingPrefix) (d : CountDisposition) (out : List Read)
    (actual : ActualAnnotation f ρ rd.1 rd.2 ann)
    (selected : fullValue f ann = some C) (count : isCountAnnotation ann = true)
    (outcome : OriginOutcome f ρ anchor (rd,ann) d out) :
    (replaceOccurrence f C rd.1 rd.2 ann).2 = rd.1.1 * d.shift := by
  cases ann with
  | zeroWeight => cases count
  | linear => cases count
  | ordinary q => cases count
  | count i q κ =>
      obtain ⟨_,rank,lam,mu,source,_⟩ := actual
      have same : f q = C := Option.some.inj selected
      have head := outcome.2
      simp only [source] at head
      by_cases identity : i = 0
      · simp only [if_pos identity] at head
        obtain ⟨_,kind,_⟩ := head
        simp [replaceOccurrence,source,same,identity,kind,Disposition.shift]
      · by_cases long : shortGapLength lam (prefixTarget mu) = 0
        · simp only [if_neg identity,if_pos long] at head
          obtain ⟨pivot,_,_,_,endForm⟩ := head
          by_cases sameRank : rank = pivot.rank
          · simp only [if_pos sameRank] at endForm
            obtain ⟨_,kind,_⟩ := endForm
            simp [replaceOccurrence,source,same,identity,long,kind,Disposition.shift]
          · simp only [if_neg sameRank] at endForm
            obtain ⟨_,h,_,_,kind,_⟩ := endForm
            simp [replaceOccurrence,source,same,identity,long,kind,Disposition.shift]
        · simp only [if_neg identity,if_neg long] at head
          obtain ⟨_,kind,_⟩ := head
          simp [replaceOccurrence,source,same,identity,long,kind,Disposition.shift,mul_add]

theorem noUnselectedShift (f : Nat → Nat) (C : Nat) (rd : Read) (ann : Annotation)
    (notCount : ¬ (fullValue f ann = some C ∧ isCountAnnotation ann = true)) :
    (replaceOccurrence f C rd.1 rd.2 ann).2 = 0 := by
  cases ann with
  | zeroWeight => rfl
  | linear => rfl
  | ordinary q =>
      by_cases same : f q = C <;> simp [replaceOccurrence,same]
  | count i q κ =>
      have different : f q ≠ C := by
        intro same
        exact notCount ⟨by simp [fullValue,same],rfl⟩
      simp [replaceOccurrence,different]

end LogicLineages.PermittedControl.ActualZeroClassOutsideAndShift
