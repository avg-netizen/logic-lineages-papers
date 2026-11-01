module
public import LogicLineages.OrdinalComparison.MultivariateIdentityDecisionTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.MultivariateProbeCode

theorem head_code (cap i : Nat) :
    positiveVariableHeadCode cap i=rawNoteEncode (positiveVariableHead cap i).1 := by
  have h0 : Nat.pair 0 (Nat.pair 0 0)=0 := by decide
  simp [positiveVariableHeadCode,positiveVariableHead,rawNoteEncode,h0]

theorem literal_code (cap i : Nat) :
    positiveVariableProbeCode cap i=
      positiveExprEncode (.head (positiveVariableHead cap i) .input) := by
  simp only [positiveVariableProbeCode,positiveExprEncode,head_code]

theorem head_primitive : Primrec₂ positiveVariableHeadCode :=
  Primrec.nat_add.comp
    (Primrec₂.natPair.comp (Primrec.const 1)
      (Primrec₂.natPair.comp (Primrec.nat_add.comp Primrec.fst Primrec.snd) (Primrec.const 0)))
    (Primrec.const 1)

theorem literal_primitive : Primrec₂ positiveVariableProbeCode :=
  Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.const 4)
      (Primrec₂.natPair.comp head_primitive (Primrec.const 1))) (Primrec.const 3)

private theorem step_primitive : Primrec (fun p : Nat × (Nat × List Nat) =>
    encodedMultivariateProbeStep p.1 p.2.1 p.2.2) := by
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
    (Primrec.ite (Primrec.eq.comp hm (Primrec.const 1)) (literal_primitive.comp hx hd)
      (Primrec.ite (Primrec.eq.comp hm (Primrec.const 2))
        (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 4)
          (Primrec₂.natPair.comp hvL hvR)) (Primrec.const 2))
        (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 4)
          (Primrec₂.natPair.comp hl hvR)) (Primrec.const 3))))

theorem primitive : Primrec₂ encodedMultivariateProbe := by
  have hs : Primrec₂ (fun cap : Nat => fun p : Nat × List Nat =>
      p.2 ++ [encodedMultivariateProbeStep cap p.1 p.2]) :=
    Primrec.list_concat.comp (Primrec.snd.comp Primrec.snd) step_primitive
  have ht : Primrec₂ encodedMultivariateProbeTable :=
    (Primrec.nat_rec (Primrec.const ([] : List Nat)) hs).of_eq (by
      intro cap n
      induction n with
      | zero => rfl
      | succ n ih =>
        change Nat.rec (motive := fun _ => List Nat) []
          (fun k table => table ++ [encodedMultivariateProbeStep cap k table]) n ++
          [encodedMultivariateProbeStep cap n (Nat.rec (motive := fun _ => List Nat) []
            (fun k table => table ++ [encodedMultivariateProbeStep cap k table]) n)] = _
        change Nat.rec (motive := fun _ => List Nat) []
          (fun k table => table ++ [encodedMultivariateProbeStep cap k table]) n = _ at ih
        rw [ih]
        rfl)
  exact (Primrec.list_getD 0).comp
    (ht.comp Primrec.fst (Primrec.succ.comp Primrec.snd)) Primrec.snd

private theorem table_length (cap n : Nat) :
    (encodedMultivariateProbeTable cap n).length=n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [encodedMultivariateProbeTable,ih]

private theorem step_correct (E : MultivariatePositiveExpr) (cap : Nat) (table : List Nat)
    (ht : ∀ F : MultivariatePositiveExpr, multivariatePositiveEncode F<multivariatePositiveEncode E →
      table.getD (multivariatePositiveEncode F) 0=positiveExprEncode (multivariatePositiveProbe cap F)) :
    encodedMultivariateProbeStep cap (multivariatePositiveEncode E) table=
      positiveExprEncode (multivariatePositiveProbe cap E) := by
  cases E with
  | constant c =>
    have hm : (4*c)%4=0 := by omega
    simp [multivariatePositiveEncode,encodedMultivariateProbeStep,multivariatePositiveProbe,positiveExprEncode,hm]
  | input i =>
    have hm : (4*i+1)%4=1 := by omega
    have hd : (4*i+1)/4=i := by omega
    simp only [multivariatePositiveEncode,encodedMultivariateProbeStep,hm,hd]
    norm_num only
    exact literal_code cap i
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
    simp only [multivariatePositiveEncode,encodedMultivariateProbeStep,hm,hd,Nat.unpair_pair]
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
    simp only [multivariatePositiveEncode,encodedMultivariateProbeStep,hm,hd,Nat.unpair_pair]
    norm_num only
    rw [hE]
    rfl

private theorem table_correct (cap n : Nat) : ∀ E : MultivariatePositiveExpr,
    multivariatePositiveEncode E<n →
    (encodedMultivariateProbeTable cap n).getD (multivariatePositiveEncode E) 0=
      positiveExprEncode (multivariatePositiveProbe cap E) := by
  induction n with
  | zero => intro E h; omega
  | succ n ih =>
    intro E hE
    by_cases heq : multivariatePositiveEncode E=n
    · rw [encodedMultivariateProbeTable,List.getD_append_right _ _ _ _
        (by rw [table_length]; omega)]
      rw [table_length,heq,Nat.sub_self]
      change encodedMultivariateProbeStep cap n _=_
      simpa only [heq] using step_correct E cap (encodedMultivariateProbeTable cap n)
        (fun F hF => ih F (by omega))
    · rw [encodedMultivariateProbeTable,List.getD_append _ _ _ _
        (by rw [table_length]; omega)]
      exact ih E (by omega)

theorem correct (cap : Nat) (E : MultivariatePositiveExpr) :
    encodedMultivariateProbe cap (multivariatePositiveEncode E)=
      positiveExprEncode (multivariatePositiveProbe cap E) :=
  table_correct cap (multivariatePositiveEncode E+1) E (Nat.lt_succ_self _)

theorem full_code : Targets.MultivariateProbeCode :=
  ⟨head_primitive,primitive,head_code,correct⟩

end LogicLineages.OrdinalComparison.MultivariateProbeCode
