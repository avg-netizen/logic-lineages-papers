module
public import LogicLineages.PermittedControl.HighestPieceGeometryProof
public import LogicLineages.OrdinalComparison.EncodedNormBallProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem profile_candidates_iff (mu nu E a : NONote) :
    rawNoteEncode a.1 ∈ highestPieceCandidates (rawNoteEncode mu.1) (rawNoteEncode nu.1) (rawNoteEncode E.1) ↔
      actualOrdinalNorm a.1.repr ≤ 2+actualOrdinalNorm mu.1.repr+actualOrdinalNorm nu.1.repr ∧
      2 ≤ a.1.repr ∧ a.1.repr < E.1.repr ∧ relativeProfile mu.1.repr a.1.repr ≠ relativeProfile nu.1.repr a.1.repr := by
  have h2 : rawComparisonCode (rawNoteEncode (ONote.ofNat 2)) (rawNoteEncode a.1)=2 ↔ a.1.repr < 2 := by
    have h := (rawComparisonOrdinalCorrect (NONote.ofNat 2) a).2.2
    change rawComparisonCode (rawNoteEncode (ONote.ofNat 2)) (rawNoteEncode a.1)=2 ↔ a.1.repr < (ONote.ofNat 2).repr at h
    simpa only [ONote.repr_ofNat] using h
  have hm : rawNormCode (rawNoteEncode mu.1)=actualOrdinalNorm mu.1.repr :=
    (rawNormCodeCorrect mu.1).trans (actualOrdinalNorm_notationCorrespondence mu).symm
  have hn : rawNormCode (rawNoteEncode nu.1)=actualOrdinalNorm nu.1.repr :=
    (rawNormCodeCorrect nu.1).trans (actualOrdinalNorm_notationCorrespondence nu).symm
  unfold highestPieceCandidates
  rw [List.mem_filter]
  simp only [decide_eq_true_eq]
  rw [encodedNormalNormBallCorrect _ a.1,hm,hn,← actualOrdinalNorm_notationCorrespondence a,
    rawProfileCorrect mu a,rawProfileCorrect nu a,(rawComparisonOrdinalCorrect a E).1,h2]
  simp only [a.2,true_and,not_lt]

 theorem profile_candidates_normal (mu nu E n : Nat) (hn : n ∈ highestPieceCandidates mu nu E) :
    ONote.NF (rawNoteDecode n) :=
  ((encodedNormalNormBallDecodeCorrect _ n).mp (List.mem_filter.mp hn).1).1

 theorem largest_profile_none (l : List Nat) : chooseLargestProfileCode l=none ↔ l=[] := by
  cases l with
  | nil => simp [chooseLargestProfileCode]
  | cons a l => cases h : chooseLargestProfileCode l <;> simp [chooseLargestProfileCode,h]

 theorem largest_profile_some (l : List Nat)
    (hnormal : ∀ m ∈ l, ONote.NF (rawNoteDecode m)) (n : Nat)
    (hn : chooseLargestProfileCode l=some n) :
    n ∈ l ∧ ∀ m ∈ l, (rawNoteDecode m).repr ≤ (rawNoteDecode n).repr := by
  induction l generalizing n with
  | nil => simp [chooseLargestProfileCode] at hn
  | cons a l ih =>
    have hna := hnormal a (List.mem_cons_self)
    have hnl : ∀ m ∈ l, ONote.NF (rawNoteDecode m) := fun m hm => hnormal m (List.mem_cons_of_mem a hm)
    cases he : chooseLargestProfileCode l with
    | none =>
      have hl : l=[] := (largest_profile_none l).mp he
      subst l
      simp [chooseLargestProfileCode] at hn
      subst n
      refine ⟨List.mem_cons_self,?_⟩
      intro m hm
      have he : m=a := by simpa using hm
      subst m
      exact le_rfl
    | some b =>
      have hb := ih hnl b he
      have hnb := hnl b hb.1
      have hcmp := (rawComparisonOrdinalCorrect (⟨rawNoteDecode a,hna⟩ : NONote)
        (⟨rawNoteDecode b,hnb⟩ : NONote)).2.2
      change rawComparisonCode (rawNoteEncode (rawNoteDecode a)) (rawNoteEncode (rawNoteDecode b))=2 ↔ (rawNoteDecode b).repr < (rawNoteDecode a).repr at hcmp
      rw [rawNoteEncodeDecode,rawNoteEncodeDecode] at hcmp
      by_cases hc : rawComparisonCode a b=2
      · simp only [chooseLargestProfileCode,he,hc,↓reduceIte,Option.some.injEq] at hn
        subst n
        refine ⟨List.mem_cons_self,?_⟩
        intro m hm
        rcases List.mem_cons.mp hm with rfl | hm
        · exact le_rfl
        · exact (hb.2 m hm).trans (hcmp.mp hc).le
      · simp only [chooseLargestProfileCode,he,hc,↓reduceIte,Option.some.injEq] at hn
        subst n
        refine ⟨List.mem_cons_of_mem a hb.1,?_⟩
        intro m hm
        rcases List.mem_cons.mp hm with rfl | hm
        · exact le_of_not_gt (fun h => hc (hcmp.mpr h))
        · exact hb.2 m hm

 theorem highestPieceEffective : Targets.HighestPieceEffective := by
  have hmu : Primrec (fun p : Nat × Nat × Nat => p.1) := Primrec.fst
  have hnu : Primrec (fun p : Nat × Nat × Nat => p.2.1) := Primrec.fst.comp Primrec.snd
  have hE : Primrec (fun p : Nat × Nat × Nat => p.2.2) := Primrec.snd.comp Primrec.snd
  have hn : Primrec rawNormCode := Primrec.nat_iff.mpr rawNormCodePrimitiveRecursive
  have hbound := Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.const 2) (hn.comp hmu)) (hn.comp hnu)
  have hp : PrimrecRel (fun e (p : Nat × Nat × Nat) =>
      rawComparisonCode (rawNoteEncode (ONote.ofNat 2)) e ≠ 2 ∧
      rawComparisonCode e p.2.2=0 ∧ rawProfileCode p.1 e ≠ rawProfileCode p.2.1 e) := by
    have hm : Primrec (fun p : Nat × (Nat × Nat × Nat) => p.2.1) := hmu.comp Primrec.snd
    have hv : Primrec (fun p : Nat × (Nat × Nat × Nat) => p.2.2.1) := hnu.comp Primrec.snd
    have he : Primrec (fun p : Nat × (Nat × Nat × Nat) => p.2.2.2) := hE.comp Primrec.snd
    exact ((Primrec.eq.comp (rawComparisonPrimitiveRecursive.comp (Primrec.const _) Primrec.fst)
      (Primrec.const 2)).not).and
      ((Primrec.eq.comp (rawComparisonPrimitiveRecursive.comp Primrec.fst he) (Primrec.const 0)).and
      ((Primrec.eq.comp (rawProfileEffective.comp hm Primrec.fst)
        (rawProfileEffective.comp hv Primrec.fst)).not))
  have hcandidates : Primrec (fun p : Nat × Nat × Nat => highestPieceCandidates p.1 p.2.1 p.2.2) :=
    hp.listFilter.comp (encodedNormalNormBallPrimitiveRecursive.comp hbound) Primrec.id
  let step : Nat → Option Nat → Option Nat := fun a ob => match ob with
    | none => some a
    | some b => some (if rawComparisonCode a b=2 then a else b)
  have hstep : Primrec₂ step := Primrec.option_casesOn Primrec.snd
    (Primrec.option_some.comp Primrec.fst)
    (Primrec.option_some.comp (Primrec.ite
      (Primrec.eq.comp (rawComparisonPrimitiveRecursive.comp (Primrec.fst.comp Primrec.fst) Primrec.snd) (Primrec.const 2))
      (Primrec.fst.comp Primrec.fst) Primrec.snd)).to₂
  have hchoose : Primrec chooseLargestProfileCode :=
    (Primrec.list_foldr Primrec.id (Primrec.const none) (hstep.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂).of_eq (by
      intro l
      induction l with
      | nil => rfl
      | cons a l ih => simp only [List.foldr_cons,ih]; rfl)
  exact hchoose.comp hcandidates

end LogicLineages.PermittedControl
