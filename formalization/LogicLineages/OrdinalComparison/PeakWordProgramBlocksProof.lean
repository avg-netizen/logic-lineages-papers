module
public import LogicLineages.OrdinalComparison.PeakWordProgramTargets
public import LogicLineages.OrdinalComparison.RawNotationCode
public import LogicLineages.OrdinalComparison.RawNormCode

@[expose] public section
namespace LogicLineages.OrdinalComparison.PeakWordProgram

private theorem replicate_primitive : Primrec₂ (fun n e : Nat => List.replicate n e) := by
  have hs : Primrec₂ (fun p : Nat × Nat => fun q : Nat × List Nat => p.2::q.2) :=
    Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd)
  have h := Primrec.nat_rec' (α := Nat × Nat) (β := List Nat) Primrec.fst (Primrec.const []) hs
  exact h.of_eq (by intro p; induction p.1 with
    | zero => rfl
    | succ n ih =>
      change p.2::Nat.rec ([] : List Nat) _ n=List.replicate (n+1) p.2
      rw [ih]
      rfl)

private theorem step_primitive : Primrec₂ encodedPrincipalBlocksStep := by
  have hp := Primrec.unpair.comp
    (Primrec.nat_sub.comp (Primrec.fst : Primrec (fun p : Nat × List (List Nat) => p.1)) (Primrec.const 1))
  have he := Primrec.fst.comp hp
  have hc := Primrec.succ.comp (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp hp)))
  have ht := Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp hp))
  exact Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0)) (Primrec.const [])
    (Primrec.list_append.comp (replicate_primitive.comp hc he)
      ((Primrec.list_getD ([] : List Nat)).comp Primrec.snd ht))

private theorem blocks_primitive : Primrec encodedPrincipalBlocks := by
  have hs : Primrec₂ (fun n : Nat => fun table : List (List Nat) =>
      table++[encodedPrincipalBlocksStep (n+1) table]) :=
    Primrec.list_concat.comp Primrec.snd (step_primitive.comp (Primrec.succ.comp Primrec.fst) Primrec.snd)
  have ht : Primrec encodedPrincipalBlocksTable :=
    (Primrec.nat_rec₁ ([[]] : List (List Nat)) hs).of_eq (by
      intro n; induction n with
      | zero => rfl
      | succ n ih =>
        change Nat.rec ([[]] : List (List Nat)) _ n++[_]=_
        rw [ih]; rfl)
  exact (Primrec.list_getD ([] : List Nat)).comp ht Primrec.id

private theorem table_length (n : Nat) : (encodedPrincipalBlocksTable n).length=n+1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [encodedPrincipalBlocksTable,ih]

private theorem step_correct (n : Nat) (table : List (List Nat))
    (ht : ∀ i<n, table.getD i []=(principalExponentBlocks (rawNoteDecode i)).map rawNoteEncode) :
    encodedPrincipalBlocksStep n table=(principalExponentBlocks (rawNoteDecode n)).map rawNoteEncode := by
  cases n with
  | zero => simp [encodedPrincipalBlocksStep,rawNoteDecode,principalExponentBlocks]
  | succ n =>
    have h := ht n.unpair.2.unpair.2
      (Nat.lt_succ_of_le ((Nat.unpair_right_le _).trans (Nat.unpair_right_le n)))
    simp only [encodedPrincipalBlocksStep,Nat.succ_ne_zero,if_false,Nat.add_sub_cancel,
      rawNoteDecode,principalExponentBlocks,List.map_append,List.map_replicate,rawNoteEncodeDecode]
    rw [h,rawNoteEncodeDecode]
    rfl

private theorem table_correct (n : Nat) : ∀ i≤n,
    (encodedPrincipalBlocksTable n).getD i []=(principalExponentBlocks (rawNoteDecode i)).map rawNoteEncode := by
  induction n with
  | zero =>
    intro i hi
    have heq : i=0 := by omega
    subst i
    simp [encodedPrincipalBlocksTable,rawNoteDecode,principalExponentBlocks]
  | succ n ih =>
    intro i hi
    by_cases hin : i≤n
    · rw [encodedPrincipalBlocksTable,List.getD_append _ _ _ _ (by rw [table_length]; omega)]
      exact ih i hin
    · have heq : i=n+1 := by omega
      subst i
      rw [encodedPrincipalBlocksTable,List.getD_append_right _ _ _ _ (by rw [table_length])]
      simp only [table_length,Nat.sub_self,List.getD_cons_zero]
      exact step_correct _ _ (fun j hj => ih j (by omega))

theorem blocks : Targets.PrincipalBlocksCodeProgram := by
  refine ⟨blocks_primitive,fun o => ?_⟩
  have h := table_correct (rawNoteEncode o) (rawNoteEncode o) le_rfl
  simpa only [encodedPrincipalBlocks,rawNoteDecodeEncode o] using h

end LogicLineages.OrdinalComparison.PeakWordProgram
