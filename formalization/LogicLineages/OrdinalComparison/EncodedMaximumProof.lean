module
public import LogicLineages.OrdinalComparison.EncodedMaximumTargets
public import LogicLineages.OrdinalComparison.EncodedNormBallProof
public import LogicLineages.OrdinalComparison.ActualMaximumPredecessor
public import Mathlib.Computability.Primrec.List

@[expose] public section

namespace LogicLineages.OrdinalComparison

private theorem comparison_decoded_less (a b : Nat)
    (ha : ONote.NF (rawNoteDecode a)) (hb : ONote.NF (rawNoteDecode b)) :
    rawComparisonCode a b = 0 ↔ (rawNoteDecode a).repr < (rawNoteDecode b).repr := by
  have h := (rawComparisonOrdinalCorrect ⟨rawNoteDecode a, ha⟩ ⟨rawNoteDecode b, hb⟩).1
  simpa only [rawNoteEncodeDecode a, rawNoteEncodeDecode b] using h

private theorem largerNormalCode_properties (a b : Nat)
    (ha : ONote.NF (rawNoteDecode a)) (hb : ONote.NF (rawNoteDecode b)) :
    ONote.NF (rawNoteDecode (largerNormalCode a b)) ∧
    (rawNoteDecode a).repr ≤ (rawNoteDecode (largerNormalCode a b)).repr ∧
    (rawNoteDecode b).repr ≤ (rawNoteDecode (largerNormalCode a b)).repr ∧
    (largerNormalCode a b = a ∨ largerNormalCode a b = b) := by
  have hc := comparison_decoded_less a b ha hb
  by_cases h : rawComparisonCode a b = 0
  · simp only [largerNormalCode, if_pos h]
    exact ⟨hb, (hc.mp h).le, le_rfl, Or.inr trivial⟩
  · simp only [largerNormalCode, if_neg h]
    exact ⟨ha, le_rfl, le_of_not_gt (fun hlt => h (hc.mpr hlt)), Or.inl trivial⟩

private theorem fold_largerNormalCode (xs : List Nat) (seed : Nat)
    (hseed : ONote.NF (rawNoteDecode seed))
    (hxs : ∀ n ∈ xs, ONote.NF (rawNoteDecode n)) :
    ONote.NF (rawNoteDecode (xs.foldl largerNormalCode seed)) ∧
    (rawNoteDecode seed).repr ≤ (rawNoteDecode (xs.foldl largerNormalCode seed)).repr ∧
    (∀ n ∈ xs, (rawNoteDecode n).repr ≤ (rawNoteDecode (xs.foldl largerNormalCode seed)).repr) ∧
    (xs.foldl largerNormalCode seed = seed ∨ xs.foldl largerNormalCode seed ∈ xs) := by
  induction xs generalizing seed with
  | nil =>
      refine ⟨hseed, le_rfl, ?_, Or.inl rfl⟩
      intro n hn
      exact False.elim (List.not_mem_nil hn)
  | cons n xs ih =>
      have hn := hxs n (List.mem_cons_self)
      have ht : ∀ m ∈ xs, ONote.NF (rawNoteDecode m) :=
        fun m hm => hxs m (List.mem_cons_of_mem n hm)
      have hc := largerNormalCode_properties seed n hseed hn
      have hi := ih (largerNormalCode seed n) hc.1 ht
      simp only [List.foldl_cons]
      refine ⟨hi.1, hc.2.1.trans hi.2.1, ?_, ?_⟩
      · intro m hm
        rcases List.mem_cons.mp hm with rfl | hm
        · exact hc.2.2.1.trans hi.2.1
        · exact hi.2.2.1 m hm
      · rcases hi.2.2.2 with heq | hmem
        · rw [heq]
          rcases hc.2.2.2 with hs | hn
          · exact Or.inl hs
          · exact Or.inr (List.mem_cons.mpr (Or.inl hn))
        · exact Or.inr (List.mem_cons_of_mem n hmem)

private theorem mem_encodedPredecessorCodes (a : NONote) (budget n : Nat) :
    n ∈ encodedPredecessorCodes (rawNoteEncode a.1) budget ↔
      ONote.NF (rawNoteDecode n) ∧ Vendor.R1.treeWeight (rawNoteDecode n) ≤ budget ∧
        (rawNoteDecode n).repr < a.1.repr := by
  simp only [encodedPredecessorCodes, List.mem_filter, decide_eq_true_eq,
    encodedNormalNormBallDecodeCorrect budget n]
  constructor
  · rintro ⟨⟨hn, hnorm⟩, hlt⟩
    have hc := (rawComparisonOrdinalCorrect ⟨rawNoteDecode n, hn⟩ a).1
    rw [rawNoteEncodeDecode n] at hc
    exact ⟨hn, hnorm, hc.mp hlt⟩
  · rintro ⟨hn, hnorm, hlt⟩
    have hc := (rawComparisonOrdinalCorrect ⟨rawNoteDecode n, hn⟩ a).1
    rw [rawNoteEncodeDecode n] at hc
    exact ⟨⟨hn, hnorm⟩, hc.mpr hlt⟩

theorem encodedMaximumPredecessorCorrect : Targets.EncodedMaximumPredecessorCorrect := by
  intro a hpos budget
  let codes := encodedPredecessorCodes (rawNoteEncode a.1) budget
  have hzero : ONote.NF (rawNoteDecode 0) := by
    rw [(rawNoteDecodeEquation).1]
    exact ONote.NF.zero
  have hcodes : ∀ n ∈ codes, ONote.NF (rawNoteDecode n) :=
    fun n hn => ((mem_encodedPredecessorCodes a budget n).mp hn).1
  have hf := fold_largerNormalCode codes 0 hzero hcodes
  let m : NONote := ⟨rawNoteDecode (codes.foldl largerNormalCode 0), hf.1⟩
  have hm : m < a ∧ Vendor.R1.treeWeight m.1 ≤ budget := by
    change (rawNoteDecode (codes.foldl largerNormalCode 0)).repr < a.1.repr ∧
      Vendor.R1.treeWeight (rawNoteDecode (codes.foldl largerNormalCode 0)) ≤ budget
    rcases hf.2.2.2 with hz | hmem
    · rw [hz, (rawNoteDecodeEquation).1]
      exact ⟨hpos, Nat.zero_le _⟩
    · have hn := (mem_encodedPredecessorCodes a budget _).mp hmem
      exact ⟨hn.2.2, hn.2.1⟩
  have hM := maximumPredecessor_correct a budget hpos
  have hMmem : rawNoteEncode (maximumPredecessor a budget).1 ∈ codes := by
    apply (mem_encodedPredecessorCodes a budget _).mpr
    rw [rawNoteDecodeEncode (maximumPredecessor a budget).1]
    exact ⟨(maximumPredecessor a budget).2, hM.1.2, hM.1.1⟩
  have hMm := hf.2.2.1 _ hMmem
  rw [rawNoteDecodeEncode (maximumPredecessor a budget).1] at hMm
  have heq : m = maximumPredecessor a budget := le_antisymm (hM.2 hm) hMm
  change codes.foldl largerNormalCode 0 = rawNoteEncode (maximumPredecessor a budget).1
  calc
    codes.foldl largerNormalCode 0 = rawNoteEncode m.1 :=
      (rawNoteEncodeDecode (codes.foldl largerNormalCode 0)).symm
    _ = rawNoteEncode (maximumPredecessor a budget).1 :=
      congrArg (fun x : NONote => rawNoteEncode x.1) heq

theorem encodedMaximumPredecessorActualCorrect : Targets.EncodedMaximumPredecessorActualCorrect := by
  intro a hpos budget
  rw [encodedMaximumPredecessorCorrect a hpos budget,
    rawNoteDecodeEncode (maximumPredecessor a budget).1]
  exact actualMaximumPredecessor_notationCorrespondence a hpos budget

theorem encodedMaximumPredecessorPrimitiveRecursive : Targets.EncodedMaximumPredecessorPrimitiveRecursive := by
  have hcmp : Primrec₂ rawComparisonCode := rawComparisonPrimitiveRecursive
  have hlist : Primrec encodedNormalNormBall := encodedNormalNormBallPrimitiveRecursive
  have hp : PrimrecRel (fun n a : Nat => rawComparisonCode n a = 0) :=
    Primrec.eq.comp hcmp (Primrec.const 0)
  have hpred : Primrec₂ encodedPredecessorCodes :=
    hp.listFilter.comp (hlist.comp Primrec.snd) Primrec.fst
  have hchoose : Primrec₂ largerNormalCode :=
    Primrec.ite (Primrec.eq.comp hcmp (Primrec.const 0)) Primrec.snd Primrec.fst
  have hfold : Primrec (fun p : (Nat × Nat) × (Nat × Nat) => largerNormalCode p.2.1 p.2.2) :=
    hchoose.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  exact Primrec.list_foldl hpred (Primrec.const 0) hfold.to₂

end LogicLineages.OrdinalComparison
