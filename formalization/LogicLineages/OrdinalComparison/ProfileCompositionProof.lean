module
public import LogicLineages.OrdinalComparison.ProfileCompositionTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.ProfileComposition

theorem source : Targets.ActualProfileCompositionSource := by
  intro L E F
  induction E with
  | constant c => exact fun _ _ => ⟨True.intro,fun _ => rfl⟩
  | input => exact fun _ hF => ⟨hF,fun _ => rfl⟩
  | add E G ihE ihG =>
    intro hE hF
    have hhE := ihE hE.1 hF
    have hhG := ihG hE.2 hF
    refine ⟨⟨hhE.1,hhG.1⟩,?_⟩
    intro x
    change actualFixedLimitProfileEval (fixedProfileCompose E F) x+
      actualFixedLimitProfileEval (fixedProfileCompose G F) x=_
    rw [hhE.2,hhG.2]
    rfl
  | head rho E ih =>
    intro hE hF
    have hh := ih hE.2.2 hF
    refine ⟨⟨hE.1,hE.2.1,hh.1⟩,?_⟩
    intro x
    change actualProfileHead rho (actualFixedLimitProfileEval (fixedProfileCompose E F) x)=_
    rw [hh.2]
    rfl

theorem support : Targets.ProfileCompositionInputSupport := by
  intro E F
  induction E with
  | constant n => rfl
  | input => rfl
  | add E G ihE ihG =>
    simp only [fixedProfileCompose,positiveExprHasInput,ihE,ihG]
    cases positiveExprHasInput E <;> cases positiveExprHasInput G <;> cases positiveExprHasInput F <;> rfl
  | head rho E ih => exact ih

private theorem step_primitive : Primrec (fun p : Nat × (Nat × List Nat) =>
    encodedProfileComposeStep p.1 p.2.1 p.2.2) := by
  have hf : Primrec (fun p : Nat × (Nat × List Nat) => p.1) := Primrec.fst
  have hn : Primrec (fun p : Nat × (Nat × List Nat) => p.2.1) := Primrec.fst.comp Primrec.snd
  have ht : Primrec (fun p : Nat × (Nat × List Nat) => p.2.2) := Primrec.snd.comp Primrec.snd
  have hm := Primrec.nat_mod.comp hn (Primrec.const 4)
  have hd := Primrec.nat_div.comp hn (Primrec.const 4)
  have hp := Primrec.unpair.comp hd
  have hl := Primrec.fst.comp hp
  have hr := Primrec.snd.comp hp
  have hvl := (Primrec.list_getD 0).comp ht hl
  have hvr := (Primrec.list_getD 0).comp ht hr
  exact Primrec.ite (Primrec.eq.comp hm (Primrec.const 0)) hn
    (Primrec.ite (Primrec.eq.comp hm (Primrec.const 1))
      (Primrec.ite (Primrec.eq.comp hn (Primrec.const 1)) hf (Primrec.const 0))
      (Primrec.ite (Primrec.eq.comp hm (Primrec.const 2))
        (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 4) (Primrec₂.natPair.comp hvl hvr)) (Primrec.const 2))
        (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 4) (Primrec₂.natPair.comp hl hvr)) (Primrec.const 3))))

private theorem program_primitive : Primrec₂ encodedProfileCompose := by
  have hs : Primrec₂ (fun f : Nat => fun p : Nat × List Nat =>
      p.2 ++ [encodedProfileComposeStep f p.1 p.2]) :=
    Primrec.list_concat.comp (Primrec.snd.comp Primrec.snd) step_primitive
  have ht : Primrec₂ encodedProfileComposeTable :=
    (Primrec.nat_rec (Primrec.const ([] : List Nat)) hs).of_eq (by
      intro f n
      induction n with
      | zero => rfl
      | succ n ih =>
        change Nat.rec (motive := fun _ => List Nat) []
          (fun k table => table ++ [encodedProfileComposeStep f k table]) n ++
          [encodedProfileComposeStep f n (Nat.rec (motive := fun _ => List Nat) []
            (fun k table => table ++ [encodedProfileComposeStep f k table]) n)] = _
        change Nat.rec (motive := fun _ => List Nat) []
          (fun k table => table ++ [encodedProfileComposeStep f k table]) n = _ at ih
        rw [ih]
        rfl)
  exact (Primrec.list_getD 0).comp
    (ht.comp Primrec.snd (Primrec.succ.comp Primrec.fst)) Primrec.fst

private theorem table_length (f n : Nat) : (encodedProfileComposeTable f n).length=n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [encodedProfileComposeTable,ih]

private theorem step_correct (E F : FixedLimitPositiveExpr) (table : List Nat)
    (ht : ∀ G : FixedLimitPositiveExpr, positiveExprEncode G<positiveExprEncode E →
      table.getD (positiveExprEncode G) 0=positiveExprEncode (fixedProfileCompose G F)) :
    encodedProfileComposeStep (positiveExprEncode F) (positiveExprEncode E) table=
      positiveExprEncode (fixedProfileCompose E F) := by
  cases E with
  | constant n =>
    have hm : (4*n)%4=0 := by omega
    simp [positiveExprEncode,encodedProfileComposeStep,fixedProfileCompose,hm]
  | input => simp [positiveExprEncode,encodedProfileComposeStep,fixedProfileCompose]
  | add E G =>
    let a := positiveExprEncode E
    let b := positiveExprEncode G
    have ha : a<4*Nat.pair a b+2 := lt_of_le_of_lt (Nat.left_le_pair a b) (by omega)
    have hb : b<4*Nat.pair a b+2 := lt_of_le_of_lt (Nat.right_le_pair a b) (by omega)
    have hE := ht E ha
    have hG := ht G hb
    have hm : (4*Nat.pair a b+2)%4=2 := by omega
    have hd : (4*Nat.pair a b+2)/4=Nat.pair a b := by omega
    dsimp only [a,b] at hm hd
    simp only [positiveExprEncode,encodedProfileComposeStep,hm,hd,Nat.unpair_pair]
    norm_num only
    rw [hE,hG]
    rfl
  | head rho E =>
    let a := rawNoteEncode rho.1
    let b := positiveExprEncode E
    have hb : b<4*Nat.pair a b+3 := lt_of_le_of_lt (Nat.right_le_pair a b) (by omega)
    have hE := ht E hb
    have hm : (4*Nat.pair a b+3)%4=3 := by omega
    have hd : (4*Nat.pair a b+3)/4=Nat.pair a b := by omega
    dsimp only [a,b] at hm hd
    simp only [positiveExprEncode,encodedProfileComposeStep,hm,hd,Nat.unpair_pair]
    norm_num only
    rw [hE]
    rfl

private theorem table_correct (F : FixedLimitPositiveExpr) (n : Nat) : ∀ E : FixedLimitPositiveExpr,
    positiveExprEncode E<n → (encodedProfileComposeTable (positiveExprEncode F) n).getD (positiveExprEncode E) 0=
      positiveExprEncode (fixedProfileCompose E F) := by
  induction n with
  | zero => intro E h; omega
  | succ n ih =>
    intro E hE
    by_cases heq : positiveExprEncode E=n
    · rw [encodedProfileComposeTable,List.getD_append_right _ _ _ _ (by rw [table_length]; omega)]
      rw [table_length,heq,Nat.sub_self]
      change encodedProfileComposeStep (positiveExprEncode F) n _=_
      simpa only [heq] using step_correct E F (encodedProfileComposeTable (positiveExprEncode F) n)
        (fun G hG => ih G (by omega))
    · rw [encodedProfileComposeTable,List.getD_append _ _ _ _ (by rw [table_length]; omega)]
      exact ih E (by omega)

theorem program : Targets.ProfileCompositionProgram :=
  ⟨program_primitive,fun E F => table_correct F (positiveExprEncode E+1) E (Nat.lt_succ_self _)⟩

end LogicLineages.OrdinalComparison.ProfileComposition
