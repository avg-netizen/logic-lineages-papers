module
public import LogicLineages.OrdinalComparison.EncodedPositiveFoldTargets
public import LogicLineages.OrdinalComparison.PositiveExprCodeProof
public import LogicLineages.OrdinalComparison.PositiveInputSupportProof
public import LogicLineages.OrdinalComparison.EncodedFiniteTailProof

@[expose] public section
namespace LogicLineages.OrdinalComparison

private noncomputable def foldStepValue (n : Nat) (table : List Nat) : Nat :=
  if n%4=0 then n/4 else if n%4=1 then 0 else
    let p := (n/4).unpair
    if n%4=2 then table.getD p.1 0 + table.getD p.2 0
    else if rawNormalCode p.1=1 then
      encodedCollapseValue (encodedFiniteTail p.1 (table.getD p.2 0)) else 0

private noncomputable def foldTableValue : Nat → List Nat
  | 0 => []
  | n+1 => foldTableValue n ++ [foldStepValue n (foldTableValue n)]

private theorem collapse_program_value (n : Nat) :
    encodedCollapsePartial n=Part.some (encodedCollapseValue n) := by
  classical
  apply Part.eq_some_iff.mpr
  unfold encodedCollapseValue
  rw [Part.getOrElse_of_dom _ (encodedCollapseTotal n) 0]
  exact Part.get_mem (encodedCollapseTotal n)

private theorem fold_step_program (n : Nat) (table : List Nat) :
    encodedPositiveFoldStep n table=Part.some (foldStepValue n table) := by
  unfold encodedPositiveFoldStep foldStepValue
  split <;> try rfl
  split <;> try rfl
  split <;> try rfl
  dsimp only
  split <;> try rfl
  exact collapse_program_value _

private theorem fold_table_program (n : Nat) :
    encodedPositiveFoldTable n=Part.some (foldTableValue n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [encodedPositiveFoldTable,ih,Part.bind_some,fold_step_program]
    rfl

private theorem fold_table_length (n : Nat) : (foldTableValue n).length=n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [foldTableValue,ih]

private theorem fold_program_value (n : Nat) :
    encodedPositiveFoldProgram n=Part.some ((foldTableValue (n+1)).getD n 0) := by
  rw [encodedPositiveFoldProgram,fold_table_program]
  rfl

private theorem computable_ite {α σ : Type} [Primcodable α] [Primcodable σ]
    {p : α → Prop} [DecidablePred p] {f g : α → σ}
    (hp : PrimrecPred p) (hf : Computable f) (hg : Computable g) :
    Computable (fun a => if p a then f a else g a) := by
  simpa only [Bool.cond_decide] using Computable.cond hp.decide.to_comp hf hg

private theorem fold_step_computable : Computable₂ foldStepValue := by
  have hm : Primrec (fun p : Nat × List Nat => p.1%4) :=
    Primrec.nat_mod.comp Primrec.fst (Primrec.const 4)
  have hd : Primrec (fun p : Nat × List Nat => p.1/4) :=
    Primrec.nat_div.comp Primrec.fst (Primrec.const 4)
  have hl := Primrec.fst.comp (Primrec.unpair.comp hd)
  have hr := Primrec.snd.comp (Primrec.unpair.comp hd)
  have hvL := (Primrec.list_getD 0).comp Primrec.snd hl
  have hvR := (Primrec.list_getD 0).comp Primrec.snd hr
  have hnorm := (Primrec.nat_iff.mpr rawNormalPrimitiveRecursive).comp hl
  have hhead := encodedCollapseComputable.comp
    (encodedFiniteTailPrimitiveRecursive.comp hl hvR).to_comp
  exact computable_ite (Primrec.eq.comp hm (Primrec.const 0)) hd.to_comp
    (computable_ite (Primrec.eq.comp hm (Primrec.const 1)) (Computable.const 0)
      (computable_ite (Primrec.eq.comp hm (Primrec.const 2))
        (Primrec.nat_add.comp hvL hvR).to_comp
        (computable_ite (Primrec.eq.comp hnorm (Primrec.const 1)) hhead (Computable.const 0))))

private theorem fold_table_computable : Computable foldTableValue := by
  have hs : Computable (fun p : Nat × List Nat => p.2 ++ [foldStepValue p.1 p.2]) :=
    Computable.list_concat.comp Computable.snd fold_step_computable
  have h := Computable.nat_rec Computable.id (Computable.const ([] : List Nat))
    (hs.comp Computable.snd).to₂
  apply h.of_eq
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    change Nat.rec [] (fun k table => table ++ [foldStepValue k table]) n ++
      [foldStepValue n (Nat.rec [] (fun k table => table ++ [foldStepValue k table]) n)] = _
    change Nat.rec [] (fun k table => table ++ [foldStepValue k table]) n = foldTableValue n at ih
    rw [ih]
    rfl

private theorem fold_result_computable : Computable
    (fun n => (foldTableValue (n+1)).getD n 0) :=
  (Primrec.list_getD 0).to_comp.comp
    (fold_table_computable.comp Primrec.succ.to_comp) Computable.id

theorem encodedPositiveFoldPartialRecursive : Targets.EncodedPositiveFoldPartialRecursive := by
  apply fold_result_computable.partrec.of_eq
  intro n
  exact (fold_program_value n).symm

theorem encodedPositiveFoldTableTotal : Targets.EncodedPositiveFoldTableTotal := by
  intro n
  refine ⟨foldTableValue n,?_,fold_table_length n⟩
  rw [fold_table_program]
  exact Part.mem_some _

private theorem fold_step_source (E : FixedLimitPositiveExpr) (table : List Nat)
    (h : ∀ F : FixedLimitPositiveExpr, positiveExprEncode F<positiveExprEncode E →
      table.getD (positiveExprEncode F) 0=actualFixedLimitProfileEval F 0) :
    foldStepValue (positiveExprEncode E) table=actualFixedLimitProfileEval E 0 := by
  cases E with
  | constant n =>
    have hm : (4*n)%4=0 := by omega
    have hd : (4*n)/4=n := by omega
    simp [positiveExprEncode,foldStepValue,hm,hd,actualFixedLimitProfileEval]
  | input => simp [positiveExprEncode,foldStepValue,actualFixedLimitProfileEval]
  | add E F =>
    let a := positiveExprEncode E
    let b := positiveExprEncode F
    have ha : a<4*Nat.pair a b+2 := lt_of_le_of_lt (Nat.left_le_pair a b) (by omega)
    have hb : b<4*Nat.pair a b+2 := lt_of_le_of_lt (Nat.right_le_pair a b) (by omega)
    have hE := h E ha
    have hF := h F hb
    have hm : (4*Nat.pair a b+2)%4=2 := by omega
    have hd : (4*Nat.pair a b+2)/4=Nat.pair a b := by omega
    dsimp only [a,b] at hm hd
    simp only [positiveExprEncode,foldStepValue,hm,hd,Nat.unpair_pair]
    norm_num only
    exact congrArg₂ (·+·) hE hF
  | head rho E =>
    let a := rawNoteEncode rho.1
    let b := positiveExprEncode E
    have hb : b<4*Nat.pair a b+3 := lt_of_le_of_lt (Nat.right_le_pair a b) (by omega)
    have hE := h E hb
    have hm : (4*Nat.pair a b+3)%4=3 := by omega
    have hd : (4*Nat.pair a b+3)/4=Nat.pair a b := by omega
    have hn : rawNormalCode a=1 := (rawNormalCorrect rho.1).mpr rho.2
    dsimp only [a,b] at hm hd hn
    simp only [positiveExprEncode,foldStepValue,hm,hd,Nat.unpair_pair]
    norm_num only
    rw [if_pos hn,hE,(encodedFiniteTailCorrect rho _).1,encodedCollapseSourceCorrect]
    change actualCollapse (finiteTail rho (actualFixedLimitProfileEval E 0)).1.repr = _
    rw [(finiteTailCorrect rho _).1]
    rfl

private theorem fold_table_source (n : Nat) : ∀ E : FixedLimitPositiveExpr,
    positiveExprEncode E<n → (foldTableValue n).getD (positiveExprEncode E) 0=
      actualFixedLimitProfileEval E 0 := by
  induction n with
  | zero => intro E h; omega
  | succ n ih =>
    intro E hE
    by_cases heq : positiveExprEncode E=n
    · rw [foldTableValue,List.getD_append_right _ _ _ _ (by rw [fold_table_length]; omega)]
      rw [fold_table_length,heq,Nat.sub_self]
      change foldStepValue n (foldTableValue n)=_
      simpa only [heq] using fold_step_source E (foldTableValue n) (fun F hF => ih F (by omega))
    · rw [foldTableValue,List.getD_append _ _ _ _ (by rw [fold_table_length]; omega)]
      exact ih E (by omega)

theorem encodedPositiveFoldCorrect : Targets.EncodedPositiveFoldCorrect := by
  intro E
  rw [fold_program_value,fold_table_source _ E (Nat.lt_succ_self _)]
  exact (Part.eq_some_iff.mpr (positiveClosedProgramCorrect E)).symm

theorem encodedPositiveFoldTotal : Targets.EncodedPositiveFoldTotal := by
  intro n
  rw [fold_program_value]
  exact Part.some_dom _

theorem encodedPositiveFoldComputable : Targets.EncodedPositiveFoldComputable := by
  apply fold_result_computable.of_eq
  intro n
  unfold encodedPositiveFoldValue
  rw [fold_program_value,Part.getOrElse_some]

theorem encodedPositiveFoldSourceCorrect : Targets.EncodedPositiveFoldSourceCorrect := by
  intro E
  unfold encodedPositiveFoldValue
  rw [encodedPositiveFoldCorrect E,Part.eq_some_iff.mpr (positiveClosedProgramCorrect E),Part.getOrElse_some]

end LogicLineages.OrdinalComparison
