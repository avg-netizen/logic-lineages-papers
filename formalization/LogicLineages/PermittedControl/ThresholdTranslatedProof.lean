module
public import LogicLineages.PermittedControl.ThresholdBaseProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem threshold_offset_decision (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (E F a b : Nat) (hE : ∃u,f u=E) (hF : ∃v,f v=F)
    (hsize : (signedOffsetValue a).natAbs+(signedOffsetValue b).natAbs+2≤min E F) :
    (if numericalComparison E F=1 then signedComparisonCode a b else numericalComparison E F)=
      integerComparison ((E:Int)+signedOffsetValue a) ((F:Int)+signedOffsetValue b) := by
  have hs := actualSignedOffsetComparison f B hf E F (signedOffsetValue a) (signedOffsetValue b) hE hF hsize
  by_cases he : E=F
  · have hc := hs.2 he
    rw [(numericalComparison_one _ _).mpr he,if_pos rfl,signedComparisonCode_correct]
    unfold integerComparison
    split_ifs <;> omega
  · have hc := hs.1 he
    rw [if_neg (fun h => he ((numericalComparison_one _ _).mp h))]
    unfold numericalComparison integerComparison
    split_ifs <;> omega

 theorem translatedThresholdCorrect : Targets.TranslatedThresholdCorrect := by
  intro f B hf lp mp lq mq hp hq s x y hx hy
  have hm := translated_input_margin (intervalPairCodes lp mp lq mq) s B x y hx hy
  let u := signedTranslateCode s.1.1 x
  let v := signedTranslateCode s.1.2 y
  obtain ⟨i,j,hi,hj,hdom,hval,_⟩ := thresholdBaseCorrect f B hf lp mp lq mq hp hq u v hm.2.2.1 hm.2.2.2.1
  let E := entryNormAt f (countInitial lp.1.repr u) i
  let F := entryNormAt f (countInitial lq.1.repr v) j
  obtain ⟨i',n,_,hi',_,hEn,hEu⟩ := properEntryRange f B hf lp.1.repr mp.1.repr u
    (normalRepresentationSound lp) hp.1 hp.2.1 hp.2.2
    (threshold_original_guard lp mp lq mq B u hm.2.2.1).1
  obtain ⟨j',m,_,hj',_,hFm,hFv⟩ := properEntryRange f B hf lq.1.repr mq.1.repr v
    (normalRepresentationSound lq) hq.1 hq.2.1 hq.2.2
    (threshold_original_guard lp mp lq mq B v hm.2.2.2.1).2
  have ei := firstEntry_unique f _ _ i' i hi' hi
  have ej := firstEntry_unique f _ _ j' j hj' hj
  rw [ei] at hEn hEu
  rw [ej] at hFm hFv
  have hsize : (signedOffsetValue s.2.1).natAbs+(signedOffsetValue s.2.2).natAbs+2≤min E F := by
    have h := hm.2.2.2.2
    dsimp only [E,F,u,v] at *
    omega
  have hcode := threshold_offset_decision f B hf E F s.2.1 s.2.2 ⟨n,hEn.symm⟩ ⟨m,hFm.symm⟩ hsize
  have hmem : integerComparison ((E:Int)+signedOffsetValue s.2.1) ((F:Int)+signedOffsetValue s.2.2) ∈
      translatedThresholdProgram f ((intervalPairCodes lp mp lq mq,s),(x,y)) := by
    unfold translatedThresholdProgram
    apply (Part.mem_map_iff _).mpr
    exact ⟨numericalComparison E F,(hval _).mpr rfl,hcode⟩
  dsimp only
  simp only [← signedTranslateCode_correct]
  refine ⟨hm.1,hm.2.1,i,j,hi,hj,Part.dom_iff_mem.mpr ⟨_,hmem⟩,?_⟩
  intro c
  constructor
  · intro hc
    exact Part.mem_unique hc hmem
  · intro hc
    rw [hc]
    exact hmem

 theorem fullThreshold : Targets.FullThreshold :=
  ⟨thresholdProgramsEffective,thresholdBaseCorrect,translatedThresholdCorrect,signedOffsetTailEffective⟩

end LogicLineages.PermittedControl
