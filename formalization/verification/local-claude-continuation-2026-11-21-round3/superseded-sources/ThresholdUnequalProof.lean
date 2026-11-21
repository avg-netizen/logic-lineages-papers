module
public import LogicLineages.PermittedControl.ThresholdEndpointProof
public import LogicLineages.PermittedControl.InverseTableProof
public import LogicLineages.PermittedControl.ThresholdNumericCalibrationProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem threshold_unequal_table (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (lp mp lq mq : NONote) (hp : Targets.ProperIntervalNotes lp mp) (hq : Targets.ProperIntervalNotes lq mq)
    (x y ip iq : Nat) (hx : inverseTableTail lp mp mq (lq-mq) B≤x)
    (hy : inverseTableTail lp mp mq (lq-mq) B≤y)
    (hgap : (lq-mq).1.repr<(lp-mp).1.repr)
    (hP : FirstEntry f (countInitial lp.1.repr x) mp.1.repr ip)
    (hQ : FirstEntry f (countInitial lq.1.repr y) mq.1.repr iq) :
    mp.1.repr+(lq-mq).1.repr<lp.1.repr ∧ mp.1.repr<mp.1.repr+(lq-mq).1.repr ∧
    ∃ i h : Nat, 0<h ∧ FirstEntry f (countInitial lp.1.repr x) (mp.1.repr+(lq-mq).1.repr) i ∧
      h=entryNormAt f (countInitial lp.1.repr x) i ∧
      (h,i) ∈ fixedEntryProgram f (rawNoteEncode lp.1,
        ordinalAddCode (rawNoteEncode mp.1) (rawNoteEncode (lq-mq).1),x) ∧
      InverseTableRows (equalGapCertificateCode (rawNoteEncode mp.1) (rawNoteEncode mq.1)
        (rawNoteEncode (lq-mq).1)) y h
        (entryNormAt f (countInitial lq.1.repr y) iq) (entryNormAt f (countInitial lp.1.repr x) ip) := by
  have hd := proper_gap_note lq mq hq
  have hg : (lq-mq).1.repr<lp.1.repr-mp.1.repr := by simpa only [note_sub_repr] using hgap
  obtain ⟨hmk,hkl,i,j,p,q,lo,mid,hiQ,hi,_,hh,hj,hp',hq',_,_,_,_,_,_,_,_,hrows,_⟩ :=
    actualInverseTable f B hf lp mp mq (lq-mq) hp.1 hp.2.1 hq.2.1 hd.1 hp.2.2 hg x y hx hy
  rw [hd.2] at hq' hrows
  have ep := firstEntry_unique f _ _ p ip hp' hP
  have eq := firstEntry_unique f _ _ q iq hq' hQ
  refine ⟨hkl,hmk,i,_,hh,hi,rfl,fixed_partner_hit_mem f B hf lp mp (lq-mq) x i hd.1 hi,?_⟩
  simpa only [ep,eq] using hrows

 theorem threshold_gap_code_lt (lp mp lq mq : NONote)
    (h : (lq-mq).1.repr<(lp-mp).1.repr) :
    rawComparisonCode (ordinalSubCode (rawNoteEncode lq.1) (rawNoteEncode mq.1))
      (ordinalSubCode (rawNoteEncode lp.1) (rawNoteEncode mp.1))=0 := by
  rw [ordinal_sub_note_code,ordinal_sub_note_code]
  exact (rawComparisonOrdinalCorrect (lq-mq) (lp-mp)).1.mpr h

 theorem threshold_gap_code_eq (lp mp lq mq : NONote)
    (h : (lp-mp).1.repr=(lq-mq).1.repr) :
    rawComparisonCode (ordinalSubCode (rawNoteEncode lq.1) (rawNoteEncode mq.1))
      (ordinalSubCode (rawNoteEncode lp.1) (rawNoteEncode mp.1))=1 := by
  rw [ordinal_sub_note_code,ordinal_sub_note_code]
  exact (rawComparisonOrdinalCorrect (lq-mq) (lp-mp)).2.1.mpr h.symm

 theorem threshold_gap_code_gt (lp mp lq mq : NONote)
    (h : (lp-mp).1.repr<(lq-mq).1.repr) :
    rawComparisonCode (ordinalSubCode (rawNoteEncode lq.1) (rawNoteEncode mq.1))
      (ordinalSubCode (rawNoteEncode lp.1) (rawNoteEncode mp.1))=2 := by
  rw [ordinal_sub_note_code,ordinal_sub_note_code]
  exact (rawComparisonOrdinalCorrect (lq-mq) (lp-mp)).2.2.mpr h

end LogicLineages.PermittedControl
