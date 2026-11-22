module
public import LogicLineages.PermittedControl.ActualRankedZeroClassTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualRankedZeroClass
open OrdinalComparison FieldComparison PreparedProjection
open ActualMixedRowLeadingAnnotations ActualMixedRowLeadingSum ActualZeroClassReplacement

private theorem headContribution (f : Nat → Nat) (ρ : Nat → Nat) (C : Nat)
    (rd : Read) (ann : Annotation) (actual : ActualAnnotation f ρ rd.1 rd.2 ann) :
    (fullValue f ann = some C → NonlinearOperand rd.1.2) ∧
    (contribution f C rd.1 rd.2 ann).1 =
      if fullValue f ann = some C then leadingWeight rd else 0 := by
  cases ann with
  | zeroWeight => simp [fullValue,contribution]
  | linear => simp [fullValue,contribution]
  | ordinary q =>
      obtain ⟨_,rank,F,op,nonlinear,_,_⟩ := actual
      simp [fullValue,contribution,leadingWeight,NonlinearOperand,op,nonlinear]
  | count i q κ =>
      obtain ⟨_,rank,lam,mu,op,_⟩ := actual
      simp [fullValue,contribution,leadingWeight,NonlinearOperand,op]

private theorem memFullCons (f : Nat → Nat) (C : Nat) (ann : Annotation)
    (annotations : List Annotation) :
    C ∈ fullValues f (ann::annotations) ↔ fullValue f ann = some C ∨ C ∈ fullValues f annotations := by
  constructor
  · intro hit
    obtain ⟨a,among,key⟩ := List.mem_filterMap.mp hit
    rcases List.mem_cons.mp among with equal | tail
    · subst a
      exact .inl key
    · exact .inr (List.mem_filterMap.mpr ⟨a,tail,key⟩)
  · intro hit
    rcases hit with head | tail
    · exact List.mem_filterMap.mpr ⟨ann,List.mem_cons_self,head⟩
    · obtain ⟨a,among,key⟩ := List.mem_filterMap.mp tail
      exact List.mem_filterMap.mpr ⟨a,List.mem_cons_of_mem _ among,key⟩

theorem exactClassSelection : ExactClassSelection := by
  intro f ρ C xs annotations aligned
  induction xs generalizing annotations with
  | nil =>
      cases aligned
      simp [classLedger,classReads,fullValues,rowParts]
  | cons rd xs next =>
      cases annotations with
      | nil => cases aligned
      | cons ann annotations =>
          change AlignedAnnotations f ρ (rd.1 :: xs.map Prod.fst) (rd.2 :: xs.map Prod.snd)
            (ann::annotations) at aligned
          cases aligned with
          | cons _ _ actual tail =>
              obtain ⟨sub,ledger,charged,existsKey,coefficient⟩ := next annotations tail
              obtain ⟨headCharged,headWeight⟩ := headContribution f ρ C rd ann actual
              by_cases selected : fullValue f ann = some C
              · simp only [classLedger,classReads,if_pos selected,List.map_cons]
                refine ⟨sub.cons_cons rd,?_,?_,?_,?_⟩
                · intro item member
                  rcases List.mem_cons.mp member with equal | rest
                  · subst item
                    exact ⟨actual,selected⟩
                  · exact ledger item rest
                · intro current member
                  rcases List.mem_cons.mp member with equal | rest
                  · subst current
                    exact headCharged selected
                  · exact charged current rest
                · simp [memFullCons,selected]
                · change (contribution f C rd.1 rd.2 ann).1 +
                    (rowParts f C (xs.map Prod.fst) (xs.map Prod.snd) annotations).1 =
                    leadingWeight rd + ((classReads f C xs annotations).map leadingWeight).sum
                  rw [headWeight,if_pos selected,coefficient]
              · simp only [classLedger,classReads,if_neg selected,memFullCons,selected,false_or]
                refine ⟨sub.cons rd,ledger,charged,existsKey,?_⟩
                change (contribution f C rd.1 rd.2 ann).1 +
                    (rowParts f C (xs.map Prod.fst) (xs.map Prod.snd) annotations).1 =
                  ((classReads f C xs annotations).map leadingWeight).sum
                rw [headWeight,if_neg selected,zero_add,coefficient]

end LogicLineages.PermittedControl.ActualRankedZeroClass
