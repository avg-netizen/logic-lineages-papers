module
public import LogicLineages.PermittedControl.OrdinalEndpointCodeTargets
public import LogicLineages.OrdinalComparison.RawComparisonProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem ordinal_node_encode (e t : ONote) (c : Nat) :
    ordinalNodeCode (rawNoteEncode e) c (rawNoteEncode t)=rawNoteEncode (.oadd e ⟨c+1,by omega⟩ t) := by
  simp only [ordinalNodeCode,rawNoteEncode,PNat.mk_coe,Nat.add_sub_cancel]

 theorem ordinal_add_aux_correct (e : ONote) (c : Nat) (z : ONote) :
    ordinalAddAuxCode (rawNoteEncode e) c (rawNoteEncode z)=
      rawNoteEncode (ONote.addAux e ⟨c+1,by omega⟩ z) := by
  cases z with
  | zero => simp [ordinalAddAuxCode,ONote.addAux,rawNoteEncode,ordinalNodeCode]
  | oadd e' c' t =>
    have hc : (c' : Nat)>0 := c'.property
    simp only [ordinalAddAuxCode,rawNoteEncode,Nat.add_sub_cancel,Nat.unpair_pair,
      Nat.add_eq_zero_iff,one_ne_zero,and_false,↓reduceIte]
    rw [rawComparisonCorrect e e']
    cases he : ONote.cmp e e' <;>
      simp [ONote.addAux,he,orderingCode,ordinalNodeCode,rawNoteEncode,PNat.add_coe,PNat.mk_coe]
    omega

 theorem ordinal_add_step_correct (n : Nat) (table : List Nat)
    (h : ∀ i<n, table.getD i 0=rawNoteEncode
      (rawNoteDecode i.unpair.1+rawNoteDecode i.unpair.2)) :
    ordinalAddCodeStep n table=rawNoteEncode
      (rawNoteDecode n.unpair.1+rawNoteDecode n.unpair.2) := by
  generalize ha : n.unpair.1=a
  generalize hb : n.unpair.2=b
  have hab : Nat.pair a b=n := by rw [←ha,←hb,Nat.pair_unpair]
  cases a with
  | zero =>
    simp only [ordinalAddCodeStep,ha,hb,↓reduceIte,rawNoteDecode,ONote.zero_add]
    exact (rawNoteEncodeDecode b).symm
  | succ a =>
    have ht : Nat.pair a.unpair.2.unpair.2 b<n := by
      rw [←hab]
      exact Nat.pair_lt_pair_left _ (Nat.lt_succ_of_le
        ((Nat.unpair_right_le _).trans (Nat.unpair_right_le a)))
    have hh := h _ ht
    simp only [Nat.unpair_pair] at hh
    simp only [ordinalAddCodeStep,ha,hb,Nat.succ_ne_zero,↓reduceIte,Nat.add_sub_cancel]
    rw [hh]
    have he : a.unpair.1=rawNoteEncode (rawNoteDecode a.unpair.1) := (rawNoteEncodeDecode _).symm
    rw [he,ordinal_add_aux_correct]
    rw [rawNoteDecode,ONote.oadd_add]

 theorem ordinal_add_table_length (n : Nat) : (ordinalAddCodeTable n).length=n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [ordinalAddCodeTable,List.length_append,List.length_singleton,ih]

 theorem ordinal_add_table_correct (n : Nat) : ∀ i<n,
    (ordinalAddCodeTable n).getD i 0=rawNoteEncode
      (rawNoteDecode i.unpair.1+rawNoteDecode i.unpair.2) := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    intro i hi
    by_cases hin : i<n
    · rw [ordinalAddCodeTable,List.getD_append _ _ _ _ (by rwa [ordinal_add_table_length])]
      exact ih i hin
    · have : i=n := by omega
      subst i
      rw [ordinalAddCodeTable,List.getD_append_right _ _ _ _ (by rw [ordinal_add_table_length])]
      simp only [ordinal_add_table_length,Nat.sub_self,List.getD_cons_zero]
      exact ordinal_add_step_correct n _ ih

 theorem ordinalAddCodeLiteral (a b : Nat) :
    ordinalAddCode a b=rawNoteEncode (rawNoteDecode a+rawNoteDecode b) := by
  unfold ordinalAddCode
  simpa only [Nat.unpair_pair] using ordinal_add_table_correct (Nat.pair a b+1) (Nat.pair a b) (by omega)

end LogicLineages.PermittedControl
