module
public import LogicLineages.PermittedControl.InitialCodeTargets
public import LogicLineages.PermittedControl.OriginalUnitsProof
public import LogicLineages.PermittedControl.PureCertificateCodeProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

def syntaxUnitCodes : ONote → List Nat
  | .zero => []
  | .oadd e c t => List.replicate (c : Nat) (rawNoteEncode e) ++ syntaxUnitCodes t

 theorem unit_code_table_length (n : Nat) : (originalUnitCodeTable n).length=n+1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [originalUnitCodeTable,List.length_append,List.length_singleton,ih]

 theorem unit_code_table_correct (n : Nat) : ∀ k ≤ n,
    (originalUnitCodeTable n).getD k []=syntaxUnitCodes (rawNoteDecode k) := by
  induction n with
  | zero =>
    intro k hk
    have : k=0 := by omega
    subst k
    rfl
  | succ n ih =>
    intro k hk
    by_cases hkn : k ≤ n
    · rw [originalUnitCodeTable,List.getD_append _ _ _ _ (by rw [unit_code_table_length]; omega)]
      exact ih k hkn
    · have : k=n+1 := by omega
      subst k
      rw [originalUnitCodeTable,List.getD_append_right _ _ _ _ (by rw [unit_code_table_length])]
      simp only [unit_code_table_length,Nat.sub_self,List.getD_cons_zero]
      rw [ih _ ((Nat.unpair_right_le _).trans (Nat.unpair_right_le n)),rawNoteDecode,syntaxUnitCodes,rawNoteEncodeDecode]
      rfl

 theorem originalUnitCodes_syntax (a : ONote) : originalUnitCodes (rawNoteEncode a)=syntaxUnitCodes a := by
  rw [originalUnitCodes,unit_code_table_correct _ _ le_rfl,rawNoteDecodeEncode]

 theorem syntax_units_actual (a : ONote) (ha : ONote.NF a) :
    (syntaxUnitCodes a).map (fun n => (rawNoteDecode n).repr)=originalGapUnits a.repr ∧
      ∀ n ∈ syntaxUnitCodes a, ONote.NF (rawNoteDecode n) := by
  induction a with
  | zero => simp [syntaxUnitCodes,originalGapUnits,ONote.repr]
  | oadd e c t ihe iht =>
    have ht := iht ha.snd
    constructor
    · rw [syntaxUnitCodes,List.map_append,List.map_replicate,rawNoteDecodeEncode,ht.1,original_units_oadd e t c ha]
    · intro n hn
      rcases List.mem_append.mp hn with hn | hn
      · have he := (List.mem_replicate.mp hn).2
        rw [he,rawNoteDecodeEncode]
        exact ha.fst
      · exact ht.2 n hn

 theorem originalUnitCodeCorrect : Targets.OriginalUnitCodeCorrect := by
  intro delta
  rw [originalUnitCodes_syntax]
  exact syntax_units_actual delta.1 delta.2

 theorem originalUnitCodesEffective : Primrec originalUnitCodes := by
  let step : Nat → List (List Nat) → List (List Nat) := fun n table =>
    table ++ [List.replicate (n.unpair.2.unpair.1+1) n.unpair.1 ++ table.getD n.unpair.2.unpair.2 []]
  have hn : Primrec (fun p : Nat×List (List Nat) => p.1) := Primrec.fst
  have ht : Primrec (fun p : Nat×List (List Nat) => p.2) := Primrec.snd
  have ha := Primrec.fst.comp (Primrec.unpair.comp hn)
  have hr := Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp hn))
  have hc := Primrec.succ.comp (Primrec.fst.comp hr)
  have hb := Primrec.snd.comp hr
  have hlist : Primrec (fun p : Nat×List (List Nat) => List.replicate (p.1.unpair.2.unpair.1+1) p.1.unpair.1) :=
    (Primrec.list_map (Primrec.list_range.comp hc) (ha.comp Primrec.fst).to₂).of_eq (by intro p; simp)
  have hval := Primrec.list_append.comp hlist ((Primrec.list_getD ([] : List Nat)).comp ht hb)
  have hstep : Primrec₂ step := (Primrec.list_concat.comp ht hval).to₂
  have htable : Primrec originalUnitCodeTable := (Primrec.nat_rec₁ [[]] hstep).of_eq (by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => change step n _ = _; rw [ih]; rfl)
  exact (Primrec.list_getD ([] : List Nat)).comp htable Primrec.id

end LogicLineages.PermittedControl
