module
public import LogicLineages.PermittedControl.ActualNodeTailSupplyTargets
import LogicLineages.PermittedControl.ThresholdNoteCodeProof
import LogicLineages.PermittedControl.ActualWeightedReadNormalizationActualProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualNodeTailSupply
open OrdinalComparison FieldComparison PreparedProjection MixedSameRankResidue
open ActualMixedRowLeadingAnnotations ActualZeroClassReplacement ActualWeightedReadNormalization
open ActualShortCountCleanup ActualZeroClassCommonTail ActualReadChargeIteration
open SelectedCountOnlyClass (prefixTarget)

theorem exactAnnotationBoundCode : ExactAnnotationBoundCode := by
  intro op
  cases op with
  | coordinate rank => rfl
  | ordinary rank field => rfl
  | count rank lam mu =>
      change max (rawNormCode (rawNoteEncode lam.1)) (rawNormCode (rawNoteEncode mu.1) + 3) =
        max (actualOrdinalNorm lam.1.repr) (actualOrdinalNorm mu.1.repr + 3)
      rw [normal_norm_code lam,normal_norm_code mu]

private theorem leFiniteMax {α : Type} (cost : α → Nat) (xs : List α) (a : α)
    (member : a ∈ xs) : cost a ≤ finiteMax cost xs := by
  induction xs with
  | nil => cases member
  | cons head tail ih =>
      change cost a ≤ max (cost head) (finiteMax cost tail)
      rcases List.mem_cons.mp member with equal | rest
      · subst a
        exact Nat.le_max_left _ _
      · exact (ih rest).trans (Nat.le_max_right _ _)

private theorem termAnnotationBound (terms : List WeightedOperand) (t : WeightedOperand)
    (member : t ∈ terms) : originalAnnotationBound t.2 ≤ annotationTail terms := by
  have code : encodeWeighted t ∈ terms.map encodeWeighted :=
    List.mem_map.mpr ⟨t,member,rfl⟩
  have leBound := leFiniteMax (fun w : WeightedCode => annotationBoundCode w.2)
    (terms.map encodeWeighted) (encodeWeighted t) code
  change annotationBoundCode t.2.code ≤ annotationTail terms at leBound
  rw [exactAnnotationBoundCode t.2] at leBound
  exact leBound

private theorem readyOne (B : Nat) (ρ : Nat → Nat) (terms : List WeightedOperand)
    (t : WeightedOperand) (member : t ∈ terms) (shape : LongCountOperand t.2)
    (paid : PaidNodeTail B ρ terms) : CountTailReady ρ t.2 := by
  obtain ⟨w,op⟩ := t
  cases op with
  | coordinate rank => exact True.intro
  | ordinary rank field => exact True.intro
  | count rank lam mu =>
      have label : (⟨rank,lam,prefixTarget mu⟩ : PrefixLabel) ∈ prefixLabels terms :=
        List.mem_filterMap.mpr ⟨(w,.count rank lam mu),member,rfl⟩
      have bound := (termAnnotationBound terms (w,.count rank lam mu) member).trans
        (Nat.le_max_left (annotationTail terms) (commonTail B terms))
      exact ⟨shape,bound.trans (paid _ label)⟩

theorem exactLongNodeGuards : ExactLongNodeGuards := by
  intro B ρ xs long paid
  constructor
  · intro t member nonzero
    exact readyOne B ρ (xs.map Prod.fst) t member (long t member nonzero) paid
  · intro label member
    exact (Nat.le_max_right (annotationTail (xs.map Prod.fst)) (commonTail B (xs.map Prod.fst)))
      |>.trans (paid label member)

theorem exactNormalizedLongNodeGuards : ExactNormalizedLongNodeGuards := by
  intro f B ρ source xs paid long normalized bound
  obtain ⟨out,success,_,_,reads,_,records⟩ := (exactNormalizedReads f ρ source).2 paid
  have identical : out = xs := Option.some.inj (success.symm.trans normalized)
  subst out
  have stillLong (rd : Read) (member : rd ∈ xs) : LongCountOperand rd.1.2 := by
    obtain ⟨prior,old,key,_⟩ := (records rd member).2.2
    rw [← key]
    exact long prior old
  refine ⟨reads,stillLong,exactLongNodeGuards B ρ xs ?_ bound⟩
  intro term member _
  obtain ⟨rd,actual,key⟩ := List.mem_map.mp member
  subst term
  exact stillLong rd actual

theorem fullActualNodeTailSupply : FullActualNodeTailSupply :=
  ⟨exactAnnotationBoundCode,exactLongNodeGuards,exactNormalizedLongNodeGuards⟩

end LogicLineages.PermittedControl.ActualNodeTailSupply
