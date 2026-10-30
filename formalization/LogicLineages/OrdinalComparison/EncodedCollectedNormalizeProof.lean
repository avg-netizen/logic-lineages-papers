module
public import LogicLineages.OrdinalComparison.EncodedCollectedNormalizeTargets
public import LogicLineages.OrdinalComparison.EncodedCollectedMergeProof
public import LogicLineages.OrdinalComparison.CollectedNormalizeProof

@[expose] public section
namespace LogicLineages.OrdinalComparison

theorem encodedCollectedOpenCorrect : Targets.EncodedCollectedOpenCorrect := by
  constructor
  · have hp : Primrec (fun n : Nat => n.unpair.2.unpair) :=
      Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)
    exact (Primrec.dom_bool₂ (fun a b => a || b)).comp
      ((Primrec.dom_bool (fun a => !a)).comp (Primrec.beq.comp (Primrec.fst.comp hp) (Primrec.const 0)))
      ((Primrec.dom_bool (fun a => !a)).comp (Primrec.beq.comp (Primrec.snd.comp hp) (Primrec.const 0)))
  · intro A hv
    cases A with
    | mk c b tags =>
      simp only [encodedCollectedOpen,collectedPositiveEncode,Nat.unpair_pair,collectedPositiveSupport]
      cases tags with
      | nil => rfl
      | cons rho A a rest =>
        have hA : collectedPositiveSupport A=true := hv.2.2.2.1
        have hn : (collectedTagsEncode (.cons rho A a rest) != 0)=true := by
          apply bne_iff_ne.mpr
          simp only [collectedTagsEncode]
          omega
        rw [hn]
        simp [collectedTagsSupport,hA]

private theorem computed_ite {α σ : Type} [Primcodable α] [Primcodable σ]
    {p : α → Prop} [DecidablePred p] {f g : α → σ}
    (hp : PrimrecPred p) (hf : Computable f) (hg : Computable g) :
    Computable (fun a => if p a then f a else g a) := by
  simpa only [Bool.cond_decide] using Computable.cond hp.decide.to_comp hf hg

private theorem norm_constant_primrec : Primrec encodedCollectedConstant :=
  Primrec₂.natPair.comp Primrec.id (Primrec.const (Nat.pair 0 0))

private theorem norm_cons_primrec {α : Type} [Primcodable α] {k a r : α → Nat}
    (hk : Primrec k) (ha : Primrec a) (hr : Primrec r) :
    Primrec (fun x => encodedCollectedCons (k x) (a x) (r x)) :=
  Primrec.nat_add.comp (Primrec.const 1) (Primrec₂.natPair.comp hk (Primrec₂.natPair.comp ha hr))

private theorem norm_step_computable : Computable₂ encodedCollectedNormalizeStep := by
  have hm : Primrec (fun p : Nat × List Nat => p.1%4) :=
    Primrec.nat_mod.comp Primrec.fst (Primrec.const 4)
  have hd : Primrec (fun p : Nat × List Nat => p.1/4) :=
    Primrec.nat_div.comp Primrec.fst (Primrec.const 4)
  have hl := Primrec.fst.comp (Primrec.unpair.comp hd)
  have hr := Primrec.snd.comp (Primrec.unpair.comp hd)
  have hvL := (Primrec.list_getD 0).comp Primrec.snd hl
  have hvR := (Primrec.list_getD 0).comp Primrec.snd hr
  have hn := (Primrec.nat_iff.mpr rawNormalPrimitiveRecursive).comp hl
  have ho := encodedCollectedOpenCorrect.1.comp hvR
  have htag := Primrec₂.natPair.comp (Primrec.const 0)
    (Primrec₂.natPair.comp (Primrec.const 0)
      (norm_cons_primrec (Primrec₂.natPair.comp hl hvR) (Primrec.const 1) (Primrec.const 0)))
  have hclosed : Computable (fun p : Nat × List Nat =>
      encodedCollectedConstant (encodedPositiveFoldValue p.1)) := norm_constant_primrec.to_comp.comp
    (encodedPositiveFoldComputable.comp Computable.fst)
  exact computed_ite (Primrec.eq.comp hm (Primrec.const 0))
    (norm_constant_primrec.comp hd).to_comp
    (computed_ite (Primrec.eq.comp hm (Primrec.const 1))
      (computed_ite (Primrec.eq.comp Primrec.fst (Primrec.const 1))
        (Computable.const (Nat.pair 0 (Nat.pair 1 0))) (Computable.const (encodedCollectedConstant 0)))
      (computed_ite (Primrec.eq.comp hm (Primrec.const 2))
        (encodedCollectedAddPrimitiveRecursive.comp hvL hvR).to_comp
        (computed_ite (Primrec.eq.comp hn (Primrec.const 1))
          (computed_ite (Primrec.eq.comp ho (Primrec.const false)) hclosed htag.to_comp)
          (Computable.const (encodedCollectedConstant 0)))))

private theorem norm_table_computable : Computable encodedCollectedNormalizeTable := by
  have hs : Computable (fun p : Nat × List Nat => p.2 ++ [encodedCollectedNormalizeStep p.1 p.2]) :=
    Computable.list_concat.comp Computable.snd norm_step_computable
  have h := Computable.nat_rec Computable.id (Computable.const ([] : List Nat))
    (hs.comp Computable.snd).to₂
  apply h.of_eq
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    change Nat.rec (motive := fun _ => List Nat) [] (fun k table => table ++ [encodedCollectedNormalizeStep k table]) n ++
      [encodedCollectedNormalizeStep n
        (Nat.rec (motive := fun _ => List Nat) [] (fun k table => table ++ [encodedCollectedNormalizeStep k table]) n)] = _
    change Nat.rec (motive := fun _ => List Nat) [] (fun k table => table ++ [encodedCollectedNormalizeStep k table]) n = _ at ih
    rw [ih]
    rfl

theorem encodedCollectedNormalizeComputable : Targets.EncodedCollectedNormalizeComputable :=
  (Primrec.list_getD 0).to_comp.comp
    (norm_table_computable.comp Primrec.succ.to_comp) Computable.id

private theorem norm_table_length (n : Nat) : (encodedCollectedNormalizeTable n).length=n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [encodedCollectedNormalizeTable,ih]

private theorem norm_step_correct (E : FixedLimitPositiveExpr)
    (hv : fixedLimitProfileBelow epsilonZero E) (table : List Nat)
    (ht : ∀ F : FixedLimitPositiveExpr, fixedLimitProfileBelow epsilonZero F →
      positiveExprEncode F<positiveExprEncode E → table.getD (positiveExprEncode F) 0=
        collectedPositiveEncode (collectedPositiveNormalize F)) :
    encodedCollectedNormalizeStep (positiveExprEncode E) table=
      collectedPositiveEncode (collectedPositiveNormalize E) := by
  cases E with
  | constant n =>
    have hm : (4*n)%4=0 := by omega
    have hd : (4*n)/4=n := by omega
    simp [positiveExprEncode,encodedCollectedNormalizeStep,hm,hd,encodedCollectedConstant,
      collectedPositiveNormalize,collectedPositiveEncode,collectedTagsEncode]
  | input =>
    simp [positiveExprEncode,encodedCollectedNormalizeStep,collectedPositiveNormalize,
      collectedPositiveEncode,collectedTagsEncode]
  | add E F =>
    let a := positiveExprEncode E
    let b := positiveExprEncode F
    have ha : a<4*Nat.pair a b+2 := lt_of_le_of_lt (Nat.left_le_pair a b) (by omega)
    have hb : b<4*Nat.pair a b+2 := lt_of_le_of_lt (Nat.right_le_pair a b) (by omega)
    have hE := ht E hv.1 ha
    have hF := ht F hv.2 hb
    have hm : (4*Nat.pair a b+2)%4=2 := by omega
    have hd : (4*Nat.pair a b+2)/4=Nat.pair a b := by omega
    dsimp only [a,b] at hm hd
    simp only [positiveExprEncode,encodedCollectedNormalizeStep,hm,hd,Nat.unpair_pair]
    norm_num only
    rw [hE,hF,encodedCollectedAddCorrect]
    rfl
  | head rho E =>
    let a := rawNoteEncode rho.1
    let b := positiveExprEncode E
    have hb : b<4*Nat.pair a b+3 := lt_of_le_of_lt (Nat.right_le_pair a b) (by omega)
    have hE := ht E hv.2.2 hb
    have hm : (4*Nat.pair a b+3)%4=3 := by omega
    have hd : (4*Nat.pair a b+3)/4=Nat.pair a b := by omega
    have hn : rawNormalCode a=1 := (rawNormalCorrect rho.1).mpr rho.2
    dsimp only [a,b] at hm hd hn
    simp only [positiveExprEncode,encodedCollectedNormalizeStep,hm,hd,Nat.unpair_pair]
    norm_num only
    rw [if_pos hn,hE,encodedCollectedOpenCorrect.2 _ (collectedPositiveNormalizeValid E hv.2.2)]
    simp only [collectedPositiveNormalize,ite_false]
    by_cases hc : collectedPositiveSupport (collectedPositiveNormalize E)=false
    · rw [if_pos hc,if_pos hc]
      rfl
    · rw [if_neg hc,if_neg hc]
      rfl

private theorem norm_table_correct (n : Nat) : ∀ E : FixedLimitPositiveExpr,
    fixedLimitProfileBelow epsilonZero E → positiveExprEncode E<n →
    (encodedCollectedNormalizeTable n).getD (positiveExprEncode E) 0=
      collectedPositiveEncode (collectedPositiveNormalize E) := by
  induction n with
  | zero => intro E hv h; omega
  | succ n ih =>
    intro E hv hE
    by_cases heq : positiveExprEncode E=n
    · rw [encodedCollectedNormalizeTable,List.getD_append_right _ _ _ _ (by rw [norm_table_length]; omega)]
      rw [norm_table_length,heq,Nat.sub_self]
      change encodedCollectedNormalizeStep n (encodedCollectedNormalizeTable n)=_
      simpa only [heq] using norm_step_correct E hv (encodedCollectedNormalizeTable n)
        (fun F hF hcode => ih F hF (by omega))
    · rw [encodedCollectedNormalizeTable,List.getD_append _ _ _ _ (by rw [norm_table_length]; omega)]
      exact ih E hv (by omega)

theorem encodedCollectedNormalizeCorrect : Targets.EncodedCollectedNormalizeCorrect := by
  intro E hv
  exact norm_table_correct (positiveExprEncode E+1) E hv (Nat.lt_succ_self _)

theorem encodedCollectedNormalizeSource : Targets.EncodedCollectedNormalizeSource := by
  intro E hv
  exact ⟨collectedPositiveNormalize E,collectedPositiveNormalizeValid E hv,
    (encodedCollectedNormalizeCorrect E hv).symm,collectedPositiveNormalizeValue E hv⟩

end LogicLineages.OrdinalComparison
