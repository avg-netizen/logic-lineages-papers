module
public import LogicLineages.PermittedControl.ThresholdUnequalProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem threshold_equal_comparison (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (lp mp lq mq : NONote) (hp : Targets.ProperIntervalNotes lp mp) (hq : Targets.ProperIntervalNotes lq mq)
    (x y ip iq : Nat) (hx : thresholdTailCode (intervalPairCodes lp mp lq mq) B≤x)
    (hy : thresholdTailCode (intervalPairCodes lp mp lq mq) B≤y)
    (hgap : (lp-mp).1.repr=(lq-mq).1.repr)
    (hP : FirstEntry f (countInitial lp.1.repr x) mp.1.repr ip)
    (hQ : FirstEntry f (countInitial lq.1.repr y) mq.1.repr iq) :
    numericalComparison (entryNormAt f (countInitial lp.1.repr x) ip)
      (entryNormAt f (countInitial lq.1.repr y) iq)=
      (if x<y then 0 else if y<x then 2 else
        equalGapCertificateCode (rawNoteEncode mp.1) (rawNoteEncode mq.1)
          (ordinalSubCode (rawNoteEncode lp.1) (rawNoteEncode mp.1))) := by
  have hdn : lq-mq=lp-mp := by
    apply Subtype.ext
    letI : ONote.NF (lq-mq).1 := (lq-mq).2
    letI : ONote.NF (lp-mp).1 := (lp-mp).2
    exact ONote.repr_inj.mp hgap.symm
  have hdp := proper_gap_note lp mp hp
  have hdq := proper_gap_note lq mq hq
  rw [hdn] at hdq
  have htx := threshold_left_tail lp mp lq mq B x hx
  have hty := threshold_left_tail lp mp lq mq B y hy
  rw [hdn] at htx hty
  dsimp only [inverseTableTail] at htx hty
  rw [hdp.2,hdq.2] at htx hty
  have hdiff : lp.1.repr-mp.1.repr=lq.1.repr-mq.1.repr := by simpa only [note_sub_repr] using hgap
  by_cases hxy : x<y
  · rw [if_pos hxy]
    apply (numericalComparison_zero _ _).mpr
    exact inverse_input_comparison f B hf lq.1.repr mq.1.repr lp.1.repr mp.1.repr
      (normalRepresentationSound lq) (normalRepresentationSound lp) hq.1 hp.1 hq.2.1 hp.2.1 hq.2.2 hp.2.2
      hdiff.le y x iq ip (by omega) (by omega) hxy hQ hP
  · rw [if_neg hxy]
    by_cases hyx : y<x
    · rw [if_pos hyx]
      apply (numericalComparison_two _ _).mpr
      exact inverse_input_comparison f B hf lp.1.repr mp.1.repr lq.1.repr mq.1.repr
        (normalRepresentationSound lp) (normalRepresentationSound lq) hp.1 hq.1 hp.2.1 hq.2.1 hp.2.2 hq.2.2
        hdiff.symm.le x y ip iq (by omega) (by omega) hyx hP hQ
    · rw [if_neg hyx,ordinal_sub_note_code]
      have he : y=x := by omega
      subst y
      obtain ⟨i,j,hi,hj,hs0,hs1,hs2⟩ := equalGapSourceTail mp mq (lp-mp) hp.2.1 hq.2.1 hdp.1 f B hf x (by omega)
      rw [hdp.2,hdq.2] at hi hj hs0 hs1 hs2
      have ei := firstEntry_unique f _ _ i ip hi hP
      have ej := firstEntry_unique f _ _ j iq hj hQ
      have hr := equalGapCertificateEffective.2.2 (rawNoteEncode mp.1) (rawNoteEncode mq.1) (rawNoteEncode (lp-mp).1)
      rcases (show equalGapCertificateCode (rawNoteEncode mp.1) (rawNoteEncode mq.1) (rawNoteEncode (lp-mp).1)=0 ∨
        equalGapCertificateCode (rawNoteEncode mp.1) (rawNoteEncode mq.1) (rawNoteEncode (lp-mp).1)=1 ∨
        equalGapCertificateCode (rawNoteEncode mp.1) (rawNoteEncode mq.1) (rawNoteEncode (lp-mp).1)=2 by omega) with h | h | h
      · rw [h]
        apply (numericalComparison_zero _ _).mpr
        simpa only [ei,ej] using hs0 h
      · rw [h]
        apply (numericalComparison_one _ _).mpr
        simpa only [ei,ej] using hs1 h
      · rw [h]
        apply (numericalComparison_two _ _).mpr
        simpa only [ei,ej] using hs2 h

end LogicLineages.PermittedControl
