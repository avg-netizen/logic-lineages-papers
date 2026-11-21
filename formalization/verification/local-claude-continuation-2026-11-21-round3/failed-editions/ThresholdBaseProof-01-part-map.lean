module
public import LogicLineages.PermittedControl.ThresholdEqualProof
public import LogicLineages.PermittedControl.ThresholdPartialProgramsProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem thresholdBaseCorrect : Targets.ThresholdBaseCorrect := by
  intro f B hf lp mp lq mq hp hq x y hx hy
  obtain ⟨ip,hP,_⟩ := entryExistenceOrbit f B hf lp.1.repr mp.1.repr x
    (normalRepresentationSound lp) hp.1 hp.2.1 hp.2.2 (threshold_original_guard lp mp lq mq B x hx).1
  obtain ⟨iq,hQ,_⟩ := entryExistenceOrbit f B hf lq.1.repr mq.1.repr y
    (normalRepresentationSound lq) hq.1 hq.2.1 hq.2.2 (threshold_original_guard lp mp lq mq B y hy).2
  let E := entryNormAt f (countInitial lp.1.repr x) ip
  let F := entryNormAt f (countInitial lq.1.repr y) iq
  have hmain : numericalComparison E F ∈ thresholdProgram f (intervalPairCodes lp mp lq mq,(x,y)) ∧
      Targets.ActualThresholdDescription f lp mp lq mq x y E F := by
    rcases lt_trichotomy (lp-mp).1.repr (lq-mq).1.repr with hlt | heq | hgt
    · obtain ⟨hupper,hlower,k,h,hh,hHit,hNorm,hMem,hRows⟩ := threshold_unequal_table f B hf lq mq lp mp hq hp
        y x iq ip (threshold_right_tail lp mp lq mq B y hy) (threshold_right_tail lp mp lq mq B x hx) hlt hQ hP
      have hc := threshold_gap_code_gt lp mp lq mq hlt
      have hv := inverseTableDecisionCode_correct _ x h F E
        (equalGapCertificateEffective.2.2 (rawNoteEncode mq.1) (rawNoteEncode mp.1) (rawNoteEncode (lp-mp).1)) hh hRows
      constructor
      · simp only [thresholdProgram,intervalPairCodes]
        rw [hc]
        simp only [show ¬(2:Nat)=1 by omega,show ¬(2:Nat)=0 by omega,↓reduceIte]
        rw [ordinal_sub_note_code]
        apply Part.mem_map_iff.mpr
        refine ⟨(h,k),hMem,?_⟩
        exact (congrArg reverseComparisonCode hv).trans (reverseComparisonCode_correct F E)
      · unfold Targets.ActualThresholdDescription
        rw [ordinal_sub_note_code,ordinal_sub_note_code]
        have ha : lp.1.repr-mp.1.repr<lq.1.repr-mq.1.repr := by simpa only [note_sub_repr] using hlt
        simp only [note_sub_repr] at hupper hlower hHit
        refine ⟨fun h => False.elim (ha.ne h),fun h => False.elim (lt_asymm ha h),?_⟩
        intro _
        exact ⟨hlower,hupper,k,h,hHit,hNorm,hMem,hRows⟩
    · have hval := threshold_equal_comparison f B hf lp mp lq mq hp hq x y ip iq hx hy heq hP hQ
      have hc := threshold_gap_code_eq lp mp lq mq heq
      constructor
      · simp only [thresholdProgram,intervalPairCodes]
        rw [hc]
        simp only [↓reduceIte,Part.mem_some_iff]
        exact hval.symm
      · unfold Targets.ActualThresholdDescription
        have ha : lp.1.repr-mp.1.repr=lq.1.repr-mq.1.repr := by simpa only [note_sub_repr] using heq
        exact ⟨fun _ => hval,fun h => False.elim (ha.symm.not_lt h),fun h => False.elim (ha.not_lt h)⟩
    · obtain ⟨hupper,hlower,k,h,hh,hHit,hNorm,hMem,hRows⟩ := threshold_unequal_table f B hf lp mp lq mq hp hq
        x y ip iq (threshold_left_tail lp mp lq mq B x hx) (threshold_left_tail lp mp lq mq B y hy) hgt hP hQ
      have hc := threshold_gap_code_lt lp mp lq mq hgt
      have hv := inverseTableDecisionCode_correct _ y h E F
        (equalGapCertificateEffective.2.2 (rawNoteEncode mp.1) (rawNoteEncode mq.1) (rawNoteEncode (lq-mq).1)) hh hRows
      constructor
      · simp only [thresholdProgram,intervalPairCodes]
        rw [hc]
        simp only [show ¬(0:Nat)=1 by omega,↓reduceIte]
        rw [ordinal_sub_note_code]
        exact Part.mem_map_iff.mpr ⟨(h,k),hMem,hv⟩
      · unfold Targets.ActualThresholdDescription
        rw [ordinal_sub_note_code,ordinal_sub_note_code]
        have ha : lq.1.repr-mq.1.repr<lp.1.repr-mp.1.repr := by simpa only [note_sub_repr] using hgt
        simp only [note_sub_repr] at hupper hlower hHit
        refine ⟨fun h => False.elim (ha.ne h.symm),?_,fun h => False.elim (lt_asymm ha h)⟩
        intro _
        exact ⟨hlower,hupper,k,h,hHit,hNorm,hMem,hRows⟩
  refine ⟨ip,iq,hP,hQ,Part.dom_iff_mem.mpr ⟨_,hmain.1⟩,?_,hmain.2⟩
  intro c
  constructor
  · intro hc
    exact Part.mem_unique hc hmain.1
  · intro hc
    rw [hc]
    exact hmain.1

end LogicLineages.PermittedControl
