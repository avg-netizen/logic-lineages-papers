module
public import LogicLineages.PermittedControl.OrdinalAdditionCodeProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem ordinal_sub_step_correct (n : Nat) (table : List Nat)
    (h : ∀ i<n, table.getD i 0=rawNoteEncode
      (rawNoteDecode i.unpair.1-rawNoteDecode i.unpair.2)) :
    ordinalSubCodeStep n table=rawNoteEncode
      (rawNoteDecode n.unpair.1-rawNoteDecode n.unpair.2) := by
  generalize ha : n.unpair.1=a
  generalize hb : n.unpair.2=b
  have hab : Nat.pair a b=n := by rw [←ha,←hb,Nat.pair_unpair]
  cases a with
  | zero =>
    simp only [ordinalSubCodeStep,ha,hb,↓reduceIte,rawNoteDecode]
    change 0=rawNoteEncode (ONote.sub 0 (rawNoteDecode b))
    rw [ONote.sub]
    rfl
  | succ a =>
    cases b with
    | zero =>
      simp only [ordinalSubCodeStep,ha,hb,Nat.succ_ne_zero,↓reduceIte,rawNoteDecode]
      change a+1=rawNoteEncode (ONote.sub (.oadd _ _ _) 0)
      rw [ONote.sub]
      simpa only [rawNoteDecode] using (rawNoteEncodeDecode (a+1)).symm
    | succ b =>
      have ht : Nat.pair a.unpair.2.unpair.2 b.unpair.2.unpair.2<n := by
        rw [←hab]
        exact (Nat.pair_lt_pair_left _ (Nat.lt_succ_of_le
          ((Nat.unpair_right_le _).trans (Nat.unpair_right_le a)))).trans
          (Nat.pair_lt_pair_right _ (Nat.lt_succ_of_le
            ((Nat.unpair_right_le _).trans (Nat.unpair_right_le b))))
      have hh := h _ ht
      simp only [Nat.unpair_pair] at hh
      simp only [ordinalSubCodeStep,ha,hb,Nat.succ_ne_zero,↓reduceIte,Nat.add_sub_cancel]
      rw [rawComparisonCode_decodeCorrect]
      rw [rawNoteDecode,rawNoteDecode]
      change _=rawNoteEncode (ONote.sub
        (.oadd (rawNoteDecode a.unpair.1) ⟨a.unpair.2.unpair.1+1,by omega⟩ (rawNoteDecode a.unpair.2.unpair.2))
        (.oadd (rawNoteDecode b.unpair.1) ⟨b.unpair.2.unpair.1+1,by omega⟩ (rawNoteDecode b.unpair.2.unpair.2)))
      cases he : ONote.cmp (rawNoteDecode a.unpair.1) (rawNoteDecode b.unpair.1) with
      | lt => simp [ONote.sub,he,orderingCode,rawNoteEncode]
      | gt => simp [ONote.sub,he,orderingCode,rawNoteEncode,rawNoteEncodeDecode,Nat.pair_unpair]
      | eq =>
        simp only [ONote.sub,he,orderingCode,↓reduceIte]
        by_cases hc : a.unpair.2.unpair.1=b.unpair.2.unpair.1
        · simp [hc,hh]
        · by_cases hd : b.unpair.2.unpair.1<a.unpair.2.unpair.1
          · have hs : a.unpair.2.unpair.1+1-(b.unpair.2.unpair.1+1)=
                (a.unpair.2.unpair.1-b.unpair.2.unpair.1-1)+1 := by omega
            simp [hc,hd,hs,ordinalNodeCode,rawNoteEncode,rawNoteEncodeDecode]
          · have hs : a.unpair.2.unpair.1+1-(b.unpair.2.unpair.1+1)=0 := by omega
            have hne : (⟨a.unpair.2.unpair.1+1,by omega⟩ : PNat)≠⟨b.unpair.2.unpair.1+1,by omega⟩ := by
              intro heq
              have hv := congrArg (fun p : PNat => (p : Nat)) heq
              simp only at hv
              omega
            simp [hc,hd,hs,hne,rawNoteEncode]

 theorem ordinal_sub_table_length (n : Nat) : (ordinalSubCodeTable n).length=n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [ordinalSubCodeTable,List.length_append,List.length_singleton,ih]

 theorem ordinal_sub_table_correct (n : Nat) : ∀ i<n,
    (ordinalSubCodeTable n).getD i 0=rawNoteEncode
      (rawNoteDecode i.unpair.1-rawNoteDecode i.unpair.2) := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    intro i hi
    by_cases hin : i<n
    · rw [ordinalSubCodeTable,List.getD_append _ _ _ _ (by rwa [ordinal_sub_table_length])]
      exact ih i hin
    · have : i=n := by omega
      subst i
      rw [ordinalSubCodeTable,List.getD_append_right _ _ _ _ (by rw [ordinal_sub_table_length])]
      simp only [ordinal_sub_table_length,Nat.sub_self,List.getD_cons_zero]
      exact ordinal_sub_step_correct n _ ih

 theorem ordinalSubCodeLiteral (a b : Nat) :
    ordinalSubCode a b=rawNoteEncode (rawNoteDecode a-rawNoteDecode b) := by
  unfold ordinalSubCode
  simpa only [Nat.unpair_pair] using ordinal_sub_table_correct (Nat.pair a b+1) (Nat.pair a b) (by omega)

end LogicLineages.PermittedControl
