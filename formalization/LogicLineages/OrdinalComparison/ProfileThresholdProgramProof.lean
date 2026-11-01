module
public import LogicLineages.OrdinalComparison.ProfileBudgetCalibrationProof
public import LogicLineages.OrdinalComparison.RawNormCode

@[expose] public section
namespace LogicLineages.OrdinalComparison.ProfileThresholdProgram

private theorem step_primitive : Primrec (fun p : Nat × List Nat =>
    encodedProfileSyntaxBudgetStep p.1 p.2) := by
  have hn : Primrec (fun p : Nat × List Nat => p.1) := Primrec.fst
  have ht : Primrec (fun p : Nat × List Nat => p.2) := Primrec.snd
  have hm := Primrec.nat_mod.comp hn (Primrec.const 4)
  have hd := Primrec.nat_div.comp hn (Primrec.const 4)
  have hp := Primrec.unpair.comp hd
  have hl := Primrec.fst.comp hp
  have hr := Primrec.snd.comp hp
  have hvl := (Primrec.list_getD 4).comp ht hl
  have hvr := (Primrec.list_getD 4).comp ht hr
  have hnorm : Primrec rawNormCode := Primrec.nat_iff.mpr rawNormCodePrimitiveRecursive
  exact Primrec.ite (Primrec.eq.comp hm (Primrec.const 0))
    (Primrec.nat_max.comp (Primrec.const 4) hd)
    (Primrec.ite (Primrec.eq.comp hm (Primrec.const 1)) (Primrec.const 4)
      (Primrec.ite (Primrec.eq.comp hm (Primrec.const 2))
        (Primrec.nat_add.comp (Primrec.nat_add.comp hvl hvr) (Primrec.const 3))
        (Primrec.succ.comp (Primrec.nat_add.comp hvr (hnorm.comp hl)))))

private theorem program_primitive : Primrec encodedProfileSyntaxBudget := by
  have hs : Primrec₂ (fun n : Nat => fun table : List Nat =>
      table ++ [encodedProfileSyntaxBudgetStep n table]) :=
    Primrec.list_concat.comp Primrec.snd step_primitive
  have ht : Primrec encodedProfileSyntaxBudgetTable :=
    (Primrec.nat_rec₁ ([] : List Nat) hs).of_eq (by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        change Nat.rec (motive := fun _ => List Nat) []
          (fun k table => table ++ [encodedProfileSyntaxBudgetStep k table]) n ++
          [encodedProfileSyntaxBudgetStep n (Nat.rec (motive := fun _ => List Nat) []
            (fun k table => table ++ [encodedProfileSyntaxBudgetStep k table]) n)] = _
        change Nat.rec (motive := fun _ => List Nat) []
          (fun k table => table ++ [encodedProfileSyntaxBudgetStep k table]) n = _ at ih
        rw [ih]
        rfl)
  exact (Primrec.list_getD 4).comp (ht.comp Primrec.succ) Primrec.id

private theorem table_length (n : Nat) : (encodedProfileSyntaxBudgetTable n).length=n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [encodedProfileSyntaxBudgetTable,ih]

private theorem step_correct (E : FixedLimitPositiveExpr) (table : List Nat)
    (ht : ∀ F : FixedLimitPositiveExpr, positiveExprEncode F<positiveExprEncode E →
      table.getD (positiveExprEncode F) 4=fixedProfileSyntaxBudget F) :
    encodedProfileSyntaxBudgetStep (positiveExprEncode E) table=fixedProfileSyntaxBudget E := by
  cases E with
  | constant n =>
    have hm : (4*n)%4=0 := by omega
    simp [positiveExprEncode,encodedProfileSyntaxBudgetStep,fixedProfileSyntaxBudget,hm]
  | input => simp [positiveExprEncode,encodedProfileSyntaxBudgetStep,fixedProfileSyntaxBudget]
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
    simp only [positiveExprEncode,encodedProfileSyntaxBudgetStep,hm,hd,Nat.unpair_pair]
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
    simp only [positiveExprEncode,encodedProfileSyntaxBudgetStep,hm,hd,Nat.unpair_pair]
    norm_num only
    rw [hE,rawNormCodeCorrect rho.1]
    rfl

private theorem table_correct (n : Nat) : ∀ E : FixedLimitPositiveExpr,
    positiveExprEncode E<n → (encodedProfileSyntaxBudgetTable n).getD (positiveExprEncode E) 4=
      fixedProfileSyntaxBudget E := by
  induction n with
  | zero => intro E h; omega
  | succ n ih =>
    intro E hE
    by_cases heq : positiveExprEncode E=n
    · rw [encodedProfileSyntaxBudgetTable,List.getD_append_right _ _ _ _ (by rw [table_length]; omega)]
      rw [table_length,heq,Nat.sub_self]
      change encodedProfileSyntaxBudgetStep n _=_
      simpa only [heq] using step_correct E (encodedProfileSyntaxBudgetTable n)
        (fun F hF => ih F (by omega))
    · rw [encodedProfileSyntaxBudgetTable,List.getD_append _ _ _ _ (by rw [table_length]; omega)]
      exact ih E (by omega)

theorem budget_program : Targets.ProfileSyntaxBudgetProgram :=
  ⟨program_primitive,fun E => table_correct (positiveExprEncode E+1) E (Nat.lt_succ_self _)⟩

theorem supplier_program : Targets.ActualProfileSupplierTailProgram := by
  have hB : Primrec (fun p : Nat × Nat => encodedProfileSyntaxBudget p.2) :=
    program_primitive.comp Primrec.snd
  have hplus := Primrec.nat_add.comp hB (Primrec.const 5)
  have hnorm : Primrec (fun p : Nat × Nat => rawNormCode p.1) :=
    (Primrec.nat_iff.mpr rawNormCodePrimitiveRecursive).comp Primrec.fst
  refine ⟨Primrec.nat_max.comp (Primrec.nat_mul.comp hplus hplus)
    (Primrec.nat_add.comp hnorm (Primrec.const 2)),?_⟩
  intro L E
  have hc := calibration E
  have hmul := Nat.mul_le_mul hc.2.2.1 hc.2.2.2.2
  have hsquare := Nat.mul_le_mul (Nat.le_add_right (fixedProfileSyntaxBudget E) 5)
    (Nat.le_add_right (fixedProfileSyntaxBudget E) 5)
  have hlinear := Nat.le_mul_self (fixedProfileSyntaxBudget E+5)
  simp only [encodedProfileSupplierTail,budget_program.2 E,rawNormCodeCorrect L.1,
    profileDirectThreshold,profileAdjacentThreshold,profileLimitMassThreshold]
  omega

end LogicLineages.OrdinalComparison.ProfileThresholdProgram
