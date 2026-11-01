module
public import LogicLineages.OrdinalComparison.SourceDisplayedHeadsTargets
public import LogicLineages.OrdinalComparison.PositiveSourceDataSourceProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.SourceDisplayedHeads

private theorem step_primitive : Primrec (fun p : Nat × List (List (Nat × Nat)) =>
    encodedDisplayedSourceHeadsStep p.1 p.2) := by
  have hn : Primrec (fun p : Nat × List (List (Nat × Nat)) => p.1) := Primrec.fst
  have ht : Primrec (fun p : Nat × List (List (Nat × Nat)) => p.2) := Primrec.snd
  have hm := Primrec.nat_mod.comp hn (Primrec.const 4)
  have hp := Primrec.unpair.comp (Primrec.nat_div.comp hn (Primrec.const 4))
  have hl := (Primrec.list_getD ([] : List (Nat × Nat))).comp ht (Primrec.fst.comp hp)
  have hr := (Primrec.list_getD ([] : List (Nat × Nat))).comp ht (Primrec.snd.comp hp)
  have hs := Primrec.snd.comp (PositiveSourceDomain.data_primitive.comp (Primrec.snd.comp hp))
  exact Primrec.ite ((Primrec.eq.comp hm (Primrec.const 0)).or (Primrec.eq.comp hm (Primrec.const 1)))
    (Primrec.const []) (Primrec.ite (Primrec.eq.comp hm (Primrec.const 2))
      (Primrec.list_append.comp hl hr)
      (Primrec.ite (Primrec.eq.comp hs (Primrec.const 1))
        (Primrec.list_cons.comp hp (Primrec.const [])) (Primrec.const [])))

private theorem program_primitive : Primrec encodedDisplayedSourceHeads := by
  have hs : Primrec₂ (fun n : Nat => fun table : List (List (Nat × Nat)) =>
      table++[encodedDisplayedSourceHeadsStep n table]) :=
    Primrec.list_concat.comp Primrec.snd step_primitive
  have ht : Primrec encodedDisplayedSourceHeadsTable :=
    (Primrec.nat_rec₁ ([] : List (List (Nat × Nat))) hs).of_eq (by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        change Nat.rec (motive := fun _ => List (List (Nat × Nat))) []
          (fun k table => table++[encodedDisplayedSourceHeadsStep k table]) n ++
          [encodedDisplayedSourceHeadsStep n (Nat.rec (motive := fun _ => List (List (Nat × Nat))) []
            (fun k table => table++[encodedDisplayedSourceHeadsStep k table]) n)] = _
        change Nat.rec (motive := fun _ => List (List (Nat × Nat))) []
          (fun k table => table++[encodedDisplayedSourceHeadsStep k table]) n = _ at ih
        rw [ih]
        rfl)
  exact (Primrec.list_getD ([] : List (Nat × Nat))).comp (ht.comp Primrec.succ) Primrec.id

private theorem table_length (n : Nat) : (encodedDisplayedSourceHeadsTable n).length=n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [encodedDisplayedSourceHeadsTable,ih]

private theorem input_map (b : Bool) (rho : NONote) (E : FixedLimitPositiveExpr) :
    (if (if b then (1:Nat) else 0)=1 then [(rawNoteEncode rho.1,positiveExprEncode E)] else [])=
      (if b then [(rho,E)] else []).map (fun p => (rawNoteEncode p.1.1,positiveExprEncode p.2)) := by
  cases b <;> rfl

private theorem step_correct (E : FixedLimitPositiveExpr) (table : List (List (Nat × Nat)))
    (ht : ∀ F : FixedLimitPositiveExpr, positiveExprEncode F<positiveExprEncode E →
      table.getD (positiveExprEncode F) []=
        (comparisonDisplayedSourceHeads F).map (fun p => (rawNoteEncode p.1.1,positiveExprEncode p.2))) :
    encodedDisplayedSourceHeadsStep (positiveExprEncode E) table=
      (comparisonDisplayedSourceHeads E).map (fun p => (rawNoteEncode p.1.1,positiveExprEncode p.2)) := by
  cases E with
  | constant n =>
    have hm : (4*n)%4=0 := by omega
    simp [encodedDisplayedSourceHeadsStep,positiveExprEncode,comparisonDisplayedSourceHeads,hm]
  | input => rfl
  | add E F =>
    let a := positiveExprEncode E
    let b := positiveExprEncode F
    have ha : a<4*Nat.pair a b+2 := lt_of_le_of_lt (Nat.left_le_pair a b) (by omega)
    have hb : b<4*Nat.pair a b+2 := lt_of_le_of_lt (Nat.right_le_pair a b) (by omega)
    have hm : (4*Nat.pair a b+2)%4=2 := by omega
    have hd : (4*Nat.pair a b+2)/4=Nat.pair a b := by omega
    dsimp only [a,b] at ha hb hm hd
    simp only [encodedDisplayedSourceHeadsStep,positiveExprEncode,hm,hd,Nat.unpair_pair]
    norm_num only
    rw [ht E ha,ht F hb]
    simp only [false_or,if_true,if_false,comparisonDisplayedSourceHeads,List.map_append]
  | head rho E =>
    let a := rawNoteEncode rho.1
    let b := positiveExprEncode E
    have hm : (4*Nat.pair a b+3)%4=3 := by omega
    have hd : (4*Nat.pair a b+3)/4=Nat.pair a b := by omega
    dsimp only [a,b] at hm hd
    simp only [encodedDisplayedSourceHeadsStep,positiveExprEncode,hm,hd,Nat.unpair_pair]
    norm_num only
    simp only [if_false,(PositiveSourceDomain.data_program.2 E).2,comparisonDisplayedSourceHeads]
    exact input_map (positiveExprHasInput E) rho E

private theorem table_correct (n : Nat) : ∀ E : FixedLimitPositiveExpr,
    positiveExprEncode E<n → (encodedDisplayedSourceHeadsTable n).getD (positiveExprEncode E) []=
      (comparisonDisplayedSourceHeads E).map (fun p => (rawNoteEncode p.1.1,positiveExprEncode p.2)) := by
  induction n with
  | zero => intro E h; omega
  | succ n ih =>
    intro E hE
    by_cases heq : positiveExprEncode E=n
    · rw [encodedDisplayedSourceHeadsTable,List.getD_append_right _ _ _ _ (by rw [table_length]; omega)]
      rw [table_length,heq,Nat.sub_self]
      change encodedDisplayedSourceHeadsStep n _=_
      simpa only [heq] using step_correct E (encodedDisplayedSourceHeadsTable n)
        (fun F hF => ih F (by omega))
    · rw [encodedDisplayedSourceHeadsTable,List.getD_append _ _ _ _ (by rw [table_length]; omega)]
      exact ih E (by omega)

theorem program : Targets.DisplayedSourceHeadProgram :=
  ⟨program_primitive,fun E => table_correct (positiveExprEncode E+1) E (Nat.lt_succ_self _)⟩

end LogicLineages.OrdinalComparison.SourceDisplayedHeads
