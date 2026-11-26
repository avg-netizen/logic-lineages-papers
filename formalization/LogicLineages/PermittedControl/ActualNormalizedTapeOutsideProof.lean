module
public import LogicLineages.PermittedControl.ActualNormalizedTapeTargets
import LogicLineages.PermittedControl.ActualRankedZeroClassSelectionProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualNormalizedTape
open OrdinalComparison FieldComparison PreparedProjection
open ActualMixedRowLeadingAnnotations ActualZeroClassReplacement ActualZeroClassCohortTransfer
open ActualRankedZeroClass ActualWeightedReadNormalization ActualZeroClassRecombinedRow
open ActualZeroClassOutsideAndShift

private theorem outsideHead (f : Nat → Nat) (ρ : Nat → Nat) (C : Nat) (rd : Read)
    (ann : Annotation) (actual : ActualAnnotation f ρ rd.1 rd.2 ann) (weight : rd.1.1 ≠ 0) :
    (match survivingPrefix f C rd.1 ann with
    | none => (replaceOccurrence f C rd.1 rd.2 ann).1.toList
    | some _ => []) = if fullValue f ann = some C then [] else [rd] := by
  cases ann with
  | zeroWeight => exact False.elim (weight actual)
  | linear => rfl
  | ordinary q =>
      by_cases same : f q = C <;> simp [survivingPrefix,replaceOccurrence,fullValue,same]
  | count i q κ =>
      obtain ⟨_,rank,lam,mu,source,_⟩ := actual
      by_cases same : f q = C
      · by_cases zero : i = 0
        · simp [survivingPrefix,replaceOccurrence,fullValue,source,same,zero]
        · by_cases long : shortGapLength lam (SelectedCountOnlyClass.prefixTarget mu) = 0 <;>
            simp [survivingPrefix,replaceOccurrence,fullValue,source,same,zero,long]
      · simp [survivingPrefix,replaceOccurrence,fullValue,source,same]

private theorem extraKeyIgnored (keys : List LowerOperand) (xs : List Read) (head : LowerOperand)
    (fresh : head ∉ originalKeys xs) :
    removeSelectedKeys (head::keys) xs = removeSelectedKeys keys xs := by
  classical
  unfold removeSelectedKeys
  apply List.filter_congr
  intro rd member
  have different : rd.1.2 ≠ head := by
    intro same
    exact fresh (List.mem_map.mpr ⟨rd,member,same⟩)
  simp [List.mem_cons,different]

private theorem outsideOfAligned (f : Nat → Nat) (ρ : Nat → Nat) (C : Nat)
    (xs : List Read) (annotations : List Annotation)
    (aligned : AlignedAnnotations f ρ (xs.map Prod.fst) (xs.map Prod.snd) annotations)
    (unique : (originalKeys xs).Nodup) (weights : ∀ rd ∈ xs, rd.1.1 ≠ 0) :
    outsideCohort f C (xs.map Prod.fst) (xs.map Prod.snd) annotations =
      removeSelectedKeys (originalKeys (classReads f C xs annotations)) xs := by
  classical
  induction xs generalizing annotations with
  | nil => cases aligned; rfl
  | cons rd xs next =>
      cases annotations with
      | nil => cases aligned
      | cons ann annotations =>
          change AlignedAnnotations f ρ (rd.1 :: xs.map Prod.fst) (rd.2 :: xs.map Prod.snd)
            (ann::annotations) at aligned
          cases aligned with
          | cons _ _ actual rest =>
              change (rd.1.2 :: originalKeys xs).Nodup at unique
              obtain ⟨fresh,tailUnique⟩ := List.nodup_cons.mp unique
              have tailEq := next annotations rest tailUnique
                (fun prior member => weights prior (List.mem_cons_of_mem _ member))
              let keys := originalKeys (classReads f C xs annotations)
              have sub := (exactClassSelection f ρ C xs annotations rest).1
              have freshClass : rd.1.2 ∉ keys := by
                intro member
                obtain ⟨prior,among,same⟩ := List.mem_map.mp member
                exact fresh (List.mem_map.mpr ⟨prior,sub.subset among,same⟩)
              change ((match survivingPrefix f C rd.1 ann with
                | none => (replaceOccurrence f C rd.1 rd.2 ann).1.toList
                | some _ => []) ++ outsideCohort f C (xs.map Prod.fst) (xs.map Prod.snd) annotations) = _
              rw [outsideHead f ρ C rd ann actual (weights rd List.mem_cons_self),tailEq]
              by_cases selected : fullValue f ann = some C
              · have keyShape : originalKeys (classReads f C (rd::xs) (ann::annotations)) =
                    rd.1.2 :: keys := by
                  simp [originalKeys,classReads,classLedger,selected,keys]
                have skip : removeSelectedKeys (rd.1.2::keys) (rd::xs) =
                    removeSelectedKeys (rd.1.2::keys) xs := by simp [removeSelectedKeys]
                rw [if_pos selected,List.nil_append,keyShape,skip]
                exact (extraKeyIgnored keys xs rd.1.2 fresh).symm
              · have keyShape : originalKeys (classReads f C (rd::xs) (ann::annotations)) = keys := by
                  simp [originalKeys,classReads,classLedger,selected,keys]
                have keep : removeSelectedKeys keys (rd::xs) =
                    rd :: removeSelectedKeys keys xs := by simp [removeSelectedKeys,freshClass]
                rw [if_neg selected,keyShape,keep]
                rfl

theorem exactTapeOutside : ExactTapeOutside := by
  intro f ρ C raw xs annotations tape aligned
  exact outsideOfAligned f ρ C xs annotations aligned tape.unique
    (fun rd member => (tape.records rd member).2.1)

end LogicLineages.PermittedControl.ActualNormalizedTape
