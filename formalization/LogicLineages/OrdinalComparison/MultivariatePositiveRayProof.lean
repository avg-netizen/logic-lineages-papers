module
public import LogicLineages.OrdinalComparison.MultivariatePositiveRayTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.MultivariatePositiveRay

private theorem multiple_code (n : Nat) :
    positiveInputMultipleCode n=positiveExprEncode (positiveInputMultiple n) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [positiveInputMultipleCode,positiveInputMultiple,positiveExprEncode,ih]

private theorem multiple_value (n x : Nat) :
    actualFixedLimitProfileEval (positiveInputMultiple n) x=n*x := by
  induction n with
  | zero => simp [positiveInputMultiple,actualFixedLimitProfileEval]
  | succ n ih => simp [positiveInputMultiple,actualFixedLimitProfileEval,ih,Nat.succ_mul]

private theorem multiple_valid (n : Nat) :
    fixedLimitProfileBelow epsilonZero (positiveInputMultiple n) := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨ih,trivial⟩

private theorem ray_value (E : MultivariatePositiveExpr) (base x : Nat) :
    actualFixedLimitProfileEval (multivariatePositiveRay base E) x=
      actualMultivariatePositiveEval E (fun i => base^i*x) := by
  induction E with
  | constant c => rfl
  | input i => exact multiple_value _ _
  | add E F ihE ihF =>
    simp only [multivariatePositiveRay,actualFixedLimitProfileEval,actualMultivariatePositiveEval,ihE,ihF]
  | head rho E ih =>
    simp only [multivariatePositiveRay,actualFixedLimitProfileEval,actualMultivariatePositiveEval,ih]

private theorem ray_valid (d base : Nat) (E : MultivariatePositiveExpr)
    (h : multivariatePositiveValid d E) :
    fixedLimitProfileBelow epsilonZero (multivariatePositiveRay base E) := by
  induction E with
  | constant c => trivial
  | input i => exact multiple_valid _
  | add E F ihE ihF => exact ⟨ihE h.1,ihF h.2⟩
  | head rho E ih => exact ⟨h.1,h.2.1,ih h.2.2⟩

theorem source : Targets.MultivariatePositiveRaySource := by
  refine ⟨multiple_code,multiple_value,multiple_valid,ray_value,ray_valid,?_⟩
  intro base x hb hx i
  exact Nat.mul_pos (pow_pos hb i) hx

private theorem multiple_primrec : Primrec positiveInputMultipleCode := by
  have hb : Primrec₂ (fun _ : Nat => fun p : Nat × Nat =>
      4*Nat.pair p.2 1+2) :=
    Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 4)
        (Primrec₂.natPair.comp (Primrec.snd.comp Primrec.snd) (Primrec.const 1)))
      (Primrec.const 2)
  have hr := Primrec.nat_rec (Primrec.const 0 : Primrec (fun _ : Nat => 0)) hb
  have hp : Primrec₂ (fun _ : Nat => positiveInputMultipleCode) := hr.of_eq (by
    intro z n
    induction n with
    | zero => rfl
    | succ n ih =>
      change 4*Nat.pair (Nat.rec 0 (fun _ prev => 4*Nat.pair prev 1+2) n) 1+2=_
      rw [ih]
      rfl)
  exact hp.comp (Primrec.const 0) Primrec.id

private theorem ray_step_primrec : Primrec (fun p : Nat × (Nat × List Nat) =>
    encodedMultivariateRayStep p.1 p.2.1 p.2.2) := by
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
  have hpow : Primrec₂ ((· ^ ·) : Nat → Nat → Nat) := Primrec₂.unpaired'.1 Nat.Primrec.pow
  exact Primrec.ite (Primrec.eq.comp hm (Primrec.const 0)) hn
    (Primrec.ite (Primrec.eq.comp hm (Primrec.const 1))
      (multiple_primrec.comp (hpow.comp hx hd))
      (Primrec.ite (Primrec.eq.comp hm (Primrec.const 2))
        (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 4)
          (Primrec₂.natPair.comp hvL hvR)) (Primrec.const 2))
        (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 4)
          (Primrec₂.natPair.comp hl hvR)) (Primrec.const 3))))

private theorem ray_primrec : Primrec₂ encodedMultivariateRay := by
  have hs : Primrec₂ (fun base : Nat => fun p : Nat × List Nat =>
      p.2 ++ [encodedMultivariateRayStep base p.1 p.2]) :=
    Primrec.list_concat.comp (Primrec.snd.comp Primrec.snd) ray_step_primrec
  have ht : Primrec₂ encodedMultivariateRayTable :=
    (Primrec.nat_rec (Primrec.const ([] : List Nat)) hs).of_eq (by
      intro base n
      induction n with
      | zero => rfl
      | succ n ih =>
        change Nat.rec (motive := fun _ => List Nat) []
          (fun k table => table ++ [encodedMultivariateRayStep base k table]) n ++
          [encodedMultivariateRayStep base n (Nat.rec (motive := fun _ => List Nat) []
            (fun k table => table ++ [encodedMultivariateRayStep base k table]) n)] = _
        change Nat.rec (motive := fun _ => List Nat) []
          (fun k table => table ++ [encodedMultivariateRayStep base k table]) n = _ at ih
        rw [ih]
        rfl)
  exact (Primrec.list_getD 0).comp
    (ht.comp Primrec.fst (Primrec.succ.comp Primrec.snd)) Primrec.snd

private theorem ray_table_length (base n : Nat) :
    (encodedMultivariateRayTable base n).length=n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [encodedMultivariateRayTable,ih]

private theorem ray_step_correct (E : MultivariatePositiveExpr) (base : Nat) (table : List Nat)
    (ht : ∀ F : MultivariatePositiveExpr, multivariatePositiveEncode F<multivariatePositiveEncode E →
      table.getD (multivariatePositiveEncode F) 0=positiveExprEncode (multivariatePositiveRay base F)) :
    encodedMultivariateRayStep base (multivariatePositiveEncode E) table=
      positiveExprEncode (multivariatePositiveRay base E) := by
  cases E with
  | constant c =>
    have hm : (4*c)%4=0 := by omega
    simp [multivariatePositiveEncode,encodedMultivariateRayStep,multivariatePositiveRay,positiveExprEncode,hm]
  | input i =>
    have hm : (4*i+1)%4=1 := by omega
    have hd : (4*i+1)/4=i := by omega
    simp only [multivariatePositiveEncode,encodedMultivariateRayStep,hm,hd]
    norm_num only
    exact multiple_code _
  | add E F =>
    let a := multivariatePositiveEncode E
    let b := multivariatePositiveEncode F
    have ha : a<4*Nat.pair a b+2 := lt_of_le_of_lt (Nat.left_le_pair a b) (by omega)
    have hb : b<4*Nat.pair a b+2 := lt_of_le_of_lt (Nat.right_le_pair a b) (by omega)
    have hE := ht E ha
    have hF := ht F hb
    have hm : (4*Nat.pair a b+2)%4=2 := by omega
    have hd : (4*Nat.pair a b+2)/4=Nat.pair a b := by omega
    dsimp only [a,b] at hm hd
    simp only [multivariatePositiveEncode,encodedMultivariateRayStep,hm,hd,Nat.unpair_pair]
    norm_num only
    rw [hE,hF]
    rfl
  | head rho E =>
    let a := rawNoteEncode rho.1
    let b := multivariatePositiveEncode E
    have hb : b<4*Nat.pair a b+3 := lt_of_le_of_lt (Nat.right_le_pair a b) (by omega)
    have hE := ht E hb
    have hm : (4*Nat.pair a b+3)%4=3 := by omega
    have hd : (4*Nat.pair a b+3)/4=Nat.pair a b := by omega
    dsimp only [a,b] at hm hd
    simp only [multivariatePositiveEncode,encodedMultivariateRayStep,hm,hd,Nat.unpair_pair]
    norm_num only
    rw [hE]
    rfl

private theorem ray_table_correct (base n : Nat) : ∀ E : MultivariatePositiveExpr,
    multivariatePositiveEncode E<n →
    (encodedMultivariateRayTable base n).getD (multivariatePositiveEncode E) 0=
      positiveExprEncode (multivariatePositiveRay base E) := by
  induction n with
  | zero => intro E h; omega
  | succ n ih =>
    intro E hE
    by_cases heq : multivariatePositiveEncode E=n
    · rw [encodedMultivariateRayTable,List.getD_append_right _ _ _ _
        (by rw [ray_table_length]; omega)]
      rw [ray_table_length,heq,Nat.sub_self]
      change encodedMultivariateRayStep base n _=_
      simpa only [heq] using ray_step_correct E base (encodedMultivariateRayTable base n)
        (fun F hF => ih F (by omega))
    · rw [encodedMultivariateRayTable,List.getD_append _ _ _ _
        (by rw [ray_table_length]; omega)]
      exact ih E (by omega)

theorem code : Targets.MultivariatePositiveRayCode := by
  refine ⟨multiple_primrec,ray_primrec,?_⟩
  intro base E
  exact ray_table_correct base (multivariatePositiveEncode E+1) E (Nat.lt_succ_self _)

end LogicLineages.OrdinalComparison.MultivariatePositiveRay
