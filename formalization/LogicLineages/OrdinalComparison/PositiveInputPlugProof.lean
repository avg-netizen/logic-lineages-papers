module
public import LogicLineages.OrdinalComparison.PositiveInputPlugTargets
public import LogicLineages.OrdinalComparison.EncodedPositiveFoldProof

@[expose] public section
namespace LogicLineages.OrdinalComparison

theorem positiveInputPlugSource : Targets.PositiveInputPlugSource := by
  intro E x
  induction E with
  | constant n => exact ⟨fun h => h,rfl⟩
  | input => exact ⟨fun _ => trivial,rfl⟩
  | add E F ihE ihF =>
    refine ⟨fun h => ⟨ihE.1 h.1,ihF.1 h.2⟩,?_⟩
    change actualFixedLimitProfileEval (positiveInputPlug E x) 0+
      actualFixedLimitProfileEval (positiveInputPlug F x) 0=_
    rw [ihE.2,ihF.2]
    rfl
  | head rho E ih =>
    refine ⟨fun h => ⟨h.1,h.2.1,ih.1 h.2.2⟩,?_⟩
    change actualProfileHead rho (actualFixedLimitProfileEval (positiveInputPlug E x) 0)=_
    rw [ih.2]
    rfl

private theorem plug_step_primrec : Primrec (fun p : Nat × (Nat × List Nat) =>
    encodedPositivePlugStep p.1 p.2.1 p.2.2) := by
  have hx : Primrec (fun p : Nat × (Nat × List Nat) => p.1) := Primrec.fst
  have hn : Primrec (fun p : Nat × (Nat × List Nat) => p.2.1) := Primrec.fst.comp Primrec.snd
  have ht : Primrec (fun p : Nat × (Nat × List Nat) => p.2.2) := Primrec.snd.comp Primrec.snd
  have hm := Primrec.nat_mod.comp hn (Primrec.const 4)
  have hd := Primrec.nat_div.comp hn (Primrec.const 4)
  have hp := Primrec.unpair.comp hd
  have hl := Primrec.fst.comp hp
  have hr := Primrec.snd.comp hp
  have hvL := (Primrec.list_getD 0).comp ht hl
  have hvR := (Primrec.list_getD 0).comp ht hr
  exact Primrec.ite (Primrec.eq.comp hm (Primrec.const 0)) hn
    (Primrec.ite (Primrec.eq.comp hm (Primrec.const 1))
      (Primrec.ite (Primrec.eq.comp hn (Primrec.const 1))
        (Primrec.nat_mul.comp (Primrec.const 4) hx) (Primrec.const 0))
      (Primrec.ite (Primrec.eq.comp hm (Primrec.const 2))
        (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 4) (Primrec₂.natPair.comp hvL hvR)) (Primrec.const 2))
        (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 4) (Primrec₂.natPair.comp hl hvR)) (Primrec.const 3))))

theorem encodedPositivePlugPrimitiveRecursive : Targets.EncodedPositivePlugPrimitiveRecursive := by
  have hs : Primrec₂ (fun x : Nat => fun p : Nat × List Nat =>
      p.2 ++ [encodedPositivePlugStep x p.1 p.2]) :=
    Primrec.list_concat.comp (Primrec.snd.comp Primrec.snd) plug_step_primrec
  have ht : Primrec₂ encodedPositivePlugTable :=
    (Primrec.nat_rec (Primrec.const ([] : List Nat)) hs).of_eq (by
      intro x n
      induction n with
      | zero => rfl
      | succ n ih =>
        change Nat.rec (motive := fun _ => List Nat) []
          (fun k table => table ++ [encodedPositivePlugStep x k table]) n ++
          [encodedPositivePlugStep x n (Nat.rec (motive := fun _ => List Nat) []
            (fun k table => table ++ [encodedPositivePlugStep x k table]) n)] = _
        change Nat.rec (motive := fun _ => List Nat) []
          (fun k table => table ++ [encodedPositivePlugStep x k table]) n = _ at ih
        rw [ih]
        rfl)
  exact (Primrec.list_getD 0).comp
    (ht.comp Primrec.snd (Primrec.succ.comp Primrec.fst)) Primrec.fst

private theorem plug_table_length (x n : Nat) : (encodedPositivePlugTable x n).length=n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [encodedPositivePlugTable,ih]

private theorem plug_step_correct (E : FixedLimitPositiveExpr) (x : Nat) (table : List Nat)
    (ht : ∀ F : FixedLimitPositiveExpr, positiveExprEncode F<positiveExprEncode E →
      table.getD (positiveExprEncode F) 0=positiveExprEncode (positiveInputPlug F x)) :
    encodedPositivePlugStep x (positiveExprEncode E) table=positiveExprEncode (positiveInputPlug E x) := by
  cases E with
  | constant n =>
    have hm : (4*n)%4=0 := by omega
    simp [positiveExprEncode,encodedPositivePlugStep,positiveInputPlug,hm]
  | input => simp [positiveExprEncode,encodedPositivePlugStep,positiveInputPlug]
  | add E F =>
    let a := positiveExprEncode E
    let b := positiveExprEncode F
    have ha : a<4*Nat.pair a b+2 := lt_of_le_of_lt (Nat.left_le_pair a b) (by omega)
    have hb : b<4*Nat.pair a b+2 := lt_of_le_of_lt (Nat.right_le_pair a b) (by omega)
    have hE := ht E ha
    have hF := ht F hb
    have hm : (4*Nat.pair a b+2)%4=2 := by omega
    have hd : (4*Nat.pair a b+2)/4=Nat.pair a b := by omega
    dsimp only [a,b] at hm hd
    simp only [positiveExprEncode,encodedPositivePlugStep,hm,hd,Nat.unpair_pair]
    norm_num only
    rw [hE,hF]
    rfl
  | head rho E =>
    let a := rawNoteEncode rho.1
    let b := positiveExprEncode E
    have hb : b<4*Nat.pair a b+3 := lt_of_le_of_lt (Nat.right_le_pair a b) (by omega)
    have hE := ht E hb
    have hm : (4*Nat.pair a b+3)%4=3 := by omega
    have hd : (4*Nat.pair a b+3)/4=Nat.pair a b := by omega
    dsimp only [a,b] at hm hd
    simp only [positiveExprEncode,encodedPositivePlugStep,hm,hd,Nat.unpair_pair]
    norm_num only
    rw [hE]
    rfl

private theorem plug_table_correct (x n : Nat) : ∀ E : FixedLimitPositiveExpr,
    positiveExprEncode E<n → (encodedPositivePlugTable x n).getD (positiveExprEncode E) 0=
      positiveExprEncode (positiveInputPlug E x) := by
  induction n with
  | zero => intro E h; omega
  | succ n ih =>
    intro E hE
    by_cases heq : positiveExprEncode E=n
    · rw [encodedPositivePlugTable,List.getD_append_right _ _ _ _ (by rw [plug_table_length]; omega)]
      rw [plug_table_length,heq,Nat.sub_self]
      change encodedPositivePlugStep x n _=_
      simpa only [heq] using plug_step_correct E x (encodedPositivePlugTable x n)
        (fun F hF => ih F (by omega))
    · rw [encodedPositivePlugTable,List.getD_append _ _ _ _ (by rw [plug_table_length]; omega)]
      exact ih E (by omega)

theorem encodedPositivePlugCorrect : Targets.EncodedPositivePlugCorrect := by
  intro E x
  exact plug_table_correct x (positiveExprEncode E+1) E (Nat.lt_succ_self _)

theorem encodedPositiveEvaluationComputable : Targets.EncodedPositiveEvaluationComputable :=
  encodedPositiveFoldComputable.comp encodedPositivePlugPrimitiveRecursive.to_comp

theorem encodedPositiveEvaluationCorrect : Targets.EncodedPositiveEvaluationCorrect := by
  intro E x
  unfold encodedPositiveEvaluation
  rw [encodedPositivePlugCorrect E x,encodedPositiveFoldSourceCorrect (positiveInputPlug E x),
    (positiveInputPlugSource E x).2]

end LogicLineages.OrdinalComparison
