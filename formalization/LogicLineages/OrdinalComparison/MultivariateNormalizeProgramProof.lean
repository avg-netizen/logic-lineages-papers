module
public import LogicLineages.OrdinalComparison.MultivariateAdditionProgramProof
public import LogicLineages.OrdinalComparison.MultivariateClosedFoldProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.MultivariateNormalizeCode

attribute [local irreducible] Phi actualCollapse encodedMultivariateClosedValue

private theorem computable_ite {α σ : Type} [Primcodable α] [Primcodable σ]
    {p : α → Prop} [DecidablePred p] {f g : α → σ}
    (hp : PrimrecPred p) (hf : Computable f) (hg : Computable g) :
    Computable (fun a => if p a then f a else g a) := by
  simpa only [Bool.cond_decide] using Computable.cond hp.decide.to_comp hf hg

private theorem step_computable : Computable (fun p : Nat × List (Nat × Bool) =>
    encodedMultivariateNormalizeStep p.1 p.2) := by
  unfold encodedMultivariateNormalizeStep
  have hn : Primrec (fun p : Nat × List (Nat × Bool) => p.1) := Primrec.fst
  have ht : Primrec (fun p : Nat × List (Nat × Bool) => p.2) := Primrec.snd
  have hm := Primrec.nat_mod.comp hn (Primrec.const 4)
  have hd := Primrec.nat_div.comp hn (Primrec.const 4)
  have hu := Primrec.unpair.comp hd
  have hl := (Primrec.list_getD (0,false)).comp ht (Primrec.fst.comp hu)
  have hr := (Primrec.list_getD (0,false)).comp ht (Primrec.snd.comp hu)
  have hconstant := (Primrec₂.natPair.comp hd (Primrec.const 0)).pair (Primrec.const false)
  have hvariable := (Primrec₂.natPair.comp (Primrec.const 0)
    (Primrec₂.natPair.comp (coefficients.2.1.comp hd (Primrec.const 1)) (Primrec.const 0))).pair
      (Primrec.const true)
  have hadd := (addition.1.comp (Primrec.fst.comp hl) (Primrec.fst.comp hr)).pair
    (Primrec.or.comp (Primrec.snd.comp hl) (Primrec.snd.comp hr))
  have hclosed : Computable (fun p : Nat × List (Nat × Bool) =>
      (Nat.pair (encodedMultivariateClosedValue p.1) (Nat.pair 0 0),false)) :=
    (Primrec₂.natPair.to_comp.comp (MultivariateDirectNormalize.closed_fold.1.comp hn.to_comp)
      (Computable.const 0)).pair (Computable.const false)
  have hcons := Primrec.nat_add.comp (Primrec.const 1)
    (Primrec₂.natPair.comp (Primrec₂.natPair.comp (Primrec.fst.comp hu) (Primrec.fst.comp hr))
      (Primrec₂.natPair.comp (Primrec.const 1) (Primrec.const 0)))
  have hopen := (Primrec₂.natPair.comp (Primrec.const 0)
    (Primrec₂.natPair.comp (Primrec.const 0) hcons)).pair (Primrec.const true)
  exact computable_ite (Primrec.eq.comp hm (Primrec.const 0)) hconstant.to_comp
    (computable_ite (Primrec.eq.comp hm (Primrec.const 1)) hvariable.to_comp
      (computable_ite (Primrec.eq.comp hm (Primrec.const 2)) hadd.to_comp
        (computable_ite (Primrec.eq.comp (Primrec.snd.comp hr) (Primrec.const false))
          hclosed hopen.to_comp)))

attribute [local irreducible] encodedMultivariateNormalizeStep

private theorem table_computable : Computable encodedMultivariateNormalizeTable := by
  have hstep : Computable (fun p : Nat × (Nat × List (Nat × Bool)) =>
      encodedMultivariateNormalizeStep p.2.1 p.2.2) :=
    Computable.comp step_computable Computable.snd
  have hs : Computable₂ (fun _ : Nat => fun q : Nat × List (Nat × Bool) =>
      q.2 ++ [encodedMultivariateNormalizeStep q.1 q.2]) :=
    Computable.list_concat.comp (Computable.snd.comp Computable.snd) hstep
  have h := Computable.nat_rec (α := Nat) (σ := List (Nat × Bool))
    (f := id) (g := fun _ => [])
    (h := fun _ q => q.2 ++ [encodedMultivariateNormalizeStep q.1 q.2])
    Computable.id (Computable.const ([] : List (Nat × Bool))) hs
  apply h.of_eq
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    change Nat.rec (motive := fun _ => List (Nat × Bool)) []
      (fun k table => table ++ [encodedMultivariateNormalizeStep k table]) n=
        encodedMultivariateNormalizeTable n at ih
    change Nat.rec (motive := fun _ => List (Nat × Bool)) []
      (fun k table => table ++ [encodedMultivariateNormalizeStep k table]) n ++
        [encodedMultivariateNormalizeStep n (Nat.rec (motive := fun _ => List (Nat × Bool)) []
          (fun k table => table ++ [encodedMultivariateNormalizeStep k table]) n)]=_
    rw [ih]
    rfl

private theorem normalization_computable : Computable encodedMultivariateCollectedNormalize := by
  have hget : Computable (fun n : Nat =>
      (encodedMultivariateNormalizeTable (n+1)).getD n (0,false)) :=
    (Primrec.list_getD (0,false)).to_comp.comp (table_computable.comp Computable.succ) Computable.id
  exact Computable.fst.comp hget

private theorem table_length (n : Nat) : (encodedMultivariateNormalizeTable n).length=n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [encodedMultivariateNormalizeTable,ih]

private theorem step_correct (E : MultivariatePositiveExpr) (table : List (Nat × Bool))
    (ht : ∀ F : MultivariatePositiveExpr, multivariatePositiveEncode F<multivariatePositiveEncode E →
      table.getD (multivariatePositiveEncode F) (0,false)=
        (multivariateCollectedCode (multivariateCollectedNormalize F),multivariatePositiveHasInput F)) :
    encodedMultivariateNormalizeStep (multivariatePositiveEncode E) table=
      (multivariateCollectedCode (multivariateCollectedNormalize E),multivariatePositiveHasInput E) := by
  cases E with
  | constant c =>
    have hm : (4*c)%4=0 := by omega
    have hd : (4*c)/4=c := by omega
    simp [encodedMultivariateNormalizeStep,multivariatePositiveEncode,hm,hd,
      multivariateCollectedNormalize,multivariateCollectedCode,multivariateCoefficientCode,
      multivariateCollectedTagsCode,multivariatePositiveHasInput]
  | input i =>
    have hm : (4*i+1)%4=1 := by omega
    have hd : (4*i+1)/4=i := by omega
    simp [encodedMultivariateNormalizeStep,multivariatePositiveEncode,hm,hd,
      coefficients.2.2.2,multivariateCollectedNormalize,multivariateCollectedCode,
      multivariateCollectedTagsCode,multivariatePositiveHasInput]
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
    simp only [encodedMultivariateNormalizeStep,multivariatePositiveEncode,hm,hd,Nat.unpair_pair]
    norm_num only
    rw [hE,hF]
    exact congrArg (fun code => (code,multivariatePositiveHasInput E || multivariatePositiveHasInput F))
      (addition.2 (multivariateCollectedNormalize E) (multivariateCollectedNormalize F))
  | head rho E =>
    let a := rawNoteEncode rho.1
    let b := multivariatePositiveEncode E
    have hb : b<4*Nat.pair a b+3 := lt_of_le_of_lt (Nat.right_le_pair a b) (by omega)
    have hE := ht E hb
    have hm : (4*Nat.pair a b+3)%4=3 := by omega
    have hd : (4*Nat.pair a b+3)/4=Nat.pair a b := by omega
    dsimp only [a,b] at hm hd
    simp only [encodedMultivariateNormalizeStep,multivariatePositiveEncode,hm,hd,Nat.unpair_pair]
    norm_num only
    rw [hE]
    by_cases hs : multivariatePositiveHasInput E=false
    · simp [hs,multivariateCollectedNormalize,multivariatePositiveEncode,
        multivariateCollectedCode,multivariateCoefficientCode,multivariateCollectedTagsCode,
        multivariatePositiveHasInput]
    · have ht : multivariatePositiveHasInput E=true := Bool.eq_true_of_not_eq_false hs
      simp [hs,ht,multivariateCollectedNormalize,multivariateCollectedCode,
        multivariateCoefficientCode,multivariateCollectedTagsCode,encodedCollectedCons,
        multivariatePositiveHasInput,Nat.add_comm 1]

private theorem table_correct (n : Nat) : ∀ E : MultivariatePositiveExpr,
    multivariatePositiveEncode E<n →
      (encodedMultivariateNormalizeTable n).getD (multivariatePositiveEncode E) (0,false)=
        (multivariateCollectedCode (multivariateCollectedNormalize E),multivariatePositiveHasInput E) := by
  induction n with
  | zero => intro E h; omega
  | succ n ih =>
    intro E hE
    by_cases heq : multivariatePositiveEncode E=n
    · rw [encodedMultivariateNormalizeTable,List.getD_append_right _ _ _ _
        (by rw [table_length]; omega)]
      rw [table_length,heq,Nat.sub_self]
      change encodedMultivariateNormalizeStep n _=_
      simpa only [heq] using step_correct E (encodedMultivariateNormalizeTable n)
        (fun F hF => ih F (by omega))
    · rw [encodedMultivariateNormalizeTable,List.getD_append _ _ _ _
        (by rw [table_length]; omega)]
      exact ih E (by omega)

theorem normalization_program : Targets.MultivariateCollectedNormalizationProgram := by
  refine ⟨normalization_computable,?_⟩
  intro E
  exact congrArg Prod.fst (table_correct (multivariatePositiveEncode E+1) E (Nat.lt_succ_self _))

end LogicLineages.OrdinalComparison.MultivariateNormalizeCode
