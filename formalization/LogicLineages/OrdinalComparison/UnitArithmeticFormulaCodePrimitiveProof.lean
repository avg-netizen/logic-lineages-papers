module
public import LogicLineages.OrdinalComparison.UnitArithmeticFormulaCodeTargets
public import LogicLineages.OrdinalComparison.ActualArithmeticCodePrimitiveProof
public import LogicLineages.OrdinalComparison.UnitEliminationBuildCodeProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ActualHeadGraph.UnitArithmeticFormulaCode.Proof
open ArithmeticCode
attribute [local irreducible] Nat.sqrt Nat.unpair
private theorem num_pr : Primrec numeralCode := ArithmeticCode.Proof.primitiveRecursiveAlgorithms.1
private theorem var_pr : Primrec variableCode := ArithmeticCode.Proof.primitiveRecursiveAlgorithms.2.1
private theorem add_pr : Primrec₂ addCode := ArithmeticCode.Proof.primitiveRecursiveAlgorithms.2.2.1
private theorem scale_pr : Primrec₂ scaleCode := ArithmeticCode.Proof.primitiveRecursiveAlgorithms.2.2.2.1
private theorem lift_pr : Primrec₂ liftCode := ArithmeticCode.Proof.primitiveRecursiveAlgorithms.2.2.2.2.1
private theorem eq_pr : Primrec₂ eqCode := ArithmeticCode.Proof.primitiveRecursiveAlgorithms.2.2.2.2.2.1
private theorem le_pr : Primrec₂ leCode := ArithmeticCode.Proof.primitiveRecursiveAlgorithms.2.2.2.2.2.2.1
private theorem obs_pr : Primrec (fun p : Nat×Nat×List Nat×Nat=>observationCode p.1 p.2.1 p.2.2.1 p.2.2.2) := ArithmeticCode.Proof.primitiveRecursiveAlgorithms.2.2.2.2.2.2.2.1
private theorem and_pr : Primrec₂ andCode := ArithmeticCode.Proof.primitiveRecursiveAlgorithms.2.2.2.2.2.2.2.2.1
private theorem or_pr : Primrec₂ orCode := ArithmeticCode.Proof.primitiveRecursiveAlgorithms.2.2.2.2.2.2.2.2.2.1
private theorem exists_pr : Primrec existsCode := ArithmeticCode.Proof.primitiveRecursiveAlgorithms.2.2.2.2.2.2.2.2.2.2.1
private theorem conj_pr : Primrec conjunctionCode := ArithmeticCode.Proof.primitiveRecursiveAlgorithms.2.2.2.2.2.2.2.2.2.2.2.1
attribute [local irreducible] observationCode
private theorem leafData_pr : Primrec leafData :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const (0,0,0,0,0))
private theorem freeData_pr : Primrec freeData :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const ([],[],0,0))
private theorem activeData_pr : Primrec activeData :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const ([],[],0,0,0,0,0))
private theorem deleted_pr : Primrec₂ deleted :=
  Primrec.list_append.comp (Primrec.list_take.comp Primrec.fst Primrec.snd)
    (Primrec.list_drop.comp (Primrec.nat_add.comp Primrec.fst (Primrec.const 1)) Primrec.snd)
private theorem shifted_pr : Primrec₂ shifted :=
  Primrec.list_map Primrec.snd (lift_pr.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂
private theorem positive_pr : Primrec positiveVariable := add_pr.comp var_pr (Primrec.const (numeralCode 1))
private abbrev S := Nat×List Nat×Nat
private theorem leaf_pr : Primrec (fun p : S=>leafFormula p.1 p.2.1 p.2.2) := by
  have hb : Primrec (fun p : S=>leafData p.1) := leafData_pr.comp Primrec.fst
  have hn := Primrec.nat_add.comp (Primrec.fst.comp hb) (Primrec.const 2)
  have hf := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hb)))
  have hc := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hb)))
  have hxs : Primrec (fun p : S=>variableCode 2 :: variableCode 1 :: shifted 3 p.2.1) :=
    Primrec.list_cons.comp (Primrec.const _) (Primrec.list_cons.comp (Primrec.const _)
      (shifted_pr.comp (Primrec.const 3) (Primrec.fst.comp Primrec.snd)))
  have ho₁ := obs_pr.comp (hn.pair ((Primrec.fst.comp (Primrec.snd.comp hb)).pair (hxs.pair (Primrec.const (variableCode 0)))))
  have ho₂ := obs_pr.comp (hn.pair ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hb))).pair (hxs.pair (Primrec.const (variableCode 0)))))
  have hl := add_pr.comp (scale_pr.comp hf (lift_pr.comp (Primrec.const 3) (Primrec.snd.comp Primrec.snd))) (Primrec.const (positiveVariable 2))
  have hr := add_pr.comp (num_pr.comp (Primrec.nat_mul.comp hf hc)) (Primrec.const (positiveVariable 1))
  exact exists_pr.comp (exists_pr.comp (exists_pr.comp (conj_pr.comp
    (Primrec.list_cons.comp ho₁ (Primrec.list_cons.comp ho₂
      (Primrec.list_cons.comp (eq_pr.comp hl hr) (Primrec.const [])))))))
private theorem free_pr : Primrec (fun p : Nat×Nat×Nat=>freeFormula p.1 p.2.1 p.2.2) := by
  have hd : Primrec (fun p : Nat×Nat×Nat=>(freeData p.1).2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (freeData_pr.comp Primrec.fst)))
  have hr : Primrec (fun p : Nat×Nat×Nat=>liftCode 1 p.2.1) := lift_pr.comp (Primrec.const 1) (Primrec.fst.comp Primrec.snd)
  have he := eq_pr.comp (Primrec.const (positiveVariable 0))
    (add_pr.comp (scale_pr.comp (Primrec.nat_add.comp hd (Primrec.const 1)) hr) (num_pr.comp hd))
  exact exists_pr.comp (and_pr.comp (Primrec.snd.comp Primrec.snd) he)
private theorem active_pr : Primrec (fun p : Nat×Nat×Nat×Nat=>activeFormula p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hm : Primrec (fun p : Nat×Nat×Nat×Nat=>(activeData p.1).2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (activeData_pr.comp Primrec.fst)))
  have hp := Primrec.fst.comp hm
  have hd := Primrec.fst.comp (Primrec.snd.comp hm)
  have he := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hm))
  have hc := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hm))
  have hl := add_pr.comp (scale_pr.comp (Primrec.nat_mul.comp hp he) (Primrec.const (positiveVariable 1)))
    (num_pr.comp (Primrec.nat_mul.comp hd hc))
  have hr := add_pr.comp (scale_pr.comp hd (Primrec.const (positiveVariable 0)))
    (scale_pr.comp (Primrec.nat_mul.comp hp (Primrec.nat_sub.comp he hd))
      (lift_pr.comp (Primrec.const 2) (Primrec.fst.comp Primrec.snd)))
  exact exists_pr.comp (exists_pr.comp (conj_pr.comp (Primrec.list_cons.comp
    (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) (Primrec.list_cons.comp
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.list_cons.comp (eq_pr.comp hl hr) (Primrec.const []))))))
attribute [local irreducible] leafFormula freeFormula activeFormula
private def children (p : S) : List S :=
  let q := (p.1/4).unpair
  if p.1%4=1 then
    [(q.2,shifted 1 (deleted (freeData q.1).1.length p.2.1),positiveVariable 0)]
  else if p.1%4=2 then
    let ys := shifted 2 (deleted (activeData q.1).1.length p.2.1)
    [(q.2.unpair.1,ys,positiveVariable 1),(q.2.unpair.2,ys,positiveVariable 0)]
  else []
private def assemble (p : S) (rs : List Nat) : Option Nat :=
  let q := (p.1/4).unpair
  some (if p.1%4=1 then freeFormula q.1 p.2.2 (rs.getD 0 0)
    else if p.1%4=2 then activeFormula q.1 p.2.2 (rs.getD 0 0) (rs.getD 1 0)
    else leafFormula (p.1/4) p.2.1 p.2.2)
private theorem children_pr : Primrec children := by
  have hn : Primrec (fun p : S=>p.1) := Primrec.fst
  have hxs : Primrec (fun p : S=>p.2.1) := Primrec.fst.comp Primrec.snd
  have hq := Primrec.unpair.comp (Primrec.nat_div.comp hn (Primrec.const 4))
  have hf := shifted_pr.comp (Primrec.const 1) (deleted_pr.comp
    (Primrec.list_length.comp (Primrec.fst.comp (freeData_pr.comp (Primrec.fst.comp hq)))) hxs)
  have ha := shifted_pr.comp (Primrec.const 2) (deleted_pr.comp
    (Primrec.list_length.comp (Primrec.fst.comp (activeData_pr.comp (Primrec.fst.comp hq)))) hxs)
  have hpair := Primrec.unpair.comp (Primrec.snd.comp hq)
  exact Primrec.ite (Primrec.eq.comp (Primrec.nat_mod.comp hn (Primrec.const 4)) (Primrec.const 1))
    (Primrec.list_cons.comp ((Primrec.snd.comp hq).pair (hf.pair (Primrec.const (positiveVariable 0)))) (Primrec.const []))
    (Primrec.ite (Primrec.eq.comp (Primrec.nat_mod.comp hn (Primrec.const 4)) (Primrec.const 2))
      (Primrec.list_cons.comp ((Primrec.fst.comp hpair).pair (ha.pair (Primrec.const (positiveVariable 1))))
        (Primrec.list_cons.comp ((Primrec.snd.comp hpair).pair (ha.pair (Primrec.const (positiveVariable 0)))) (Primrec.const [])))
      (Primrec.const []))
private theorem assemble_pr : Primrec₂ assemble := by
  have hn : Primrec (fun p : S×List Nat=>p.1.1) := Primrec.fst.comp Primrec.fst
  have hx : Primrec (fun p : S×List Nat=>p.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hr : Primrec (fun p : S×List Nat=>p.1.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hd := Primrec.nat_div.comp hn (Primrec.const 4)
  have hq := Primrec.fst.comp (Primrec.unpair.comp hd)
  have h₀ : Primrec (fun p : S×List Nat=>p.2.getD 0 0) := (Primrec.list_getD (0 : Nat)).comp Primrec.snd (Primrec.const 0)
  have h₁ : Primrec (fun p : S×List Nat=>p.2.getD 1 0) := (Primrec.list_getD (0 : Nat)).comp Primrec.snd (Primrec.const 1)
  exact Primrec.option_some.comp (Primrec.ite
    (Primrec.eq.comp (Primrec.nat_mod.comp hn (Primrec.const 4)) (Primrec.const 1))
    (free_pr.comp (hq.pair (hr.pair h₀)))
    (Primrec.ite (Primrec.eq.comp (Primrec.nat_mod.comp hn (Primrec.const 4)) (Primrec.const 2))
      (active_pr.comp (hq.pair (hr.pair (h₀.pair h₁)))) (leaf_pr.comp (hd.pair (hx.pair hr)))))
private theorem unit_pr : Primrec (fun p : S=>unitFormulaCode p.1 p.2.1 p.2.2) := by
  apply Primrec.nat_omega_rec' (fun p : S=>unitFormulaCode p.1 p.2.1 p.2.2)
    Primrec.fst children_pr assemble_pr
  · intro p q hq
    by_cases h₁ : p.1%4=1
    · simp only [children,if_pos h₁,List.mem_singleton] at hq
      subst q
      exact (Nat.unpair_right_le _).trans_lt (Nat.div_lt_self (by omega) (by decide))
    · by_cases h₂ : p.1%4=2
      · have hd : p.1/4<p.1 := Nat.div_lt_self (by omega) (by decide)
        have hc : (p.1/4).unpair.2<p.1 := (Nat.unpair_right_le _).trans_lt hd
        simp only [children,if_neg h₁,if_pos h₂,List.mem_cons,List.not_mem_nil,or_false] at hq
        rcases hq with rfl | rfl
        · exact (Nat.unpair_left_le _).trans_lt hc
        · exact (Nat.unpair_right_le _).trans_lt hc
      · simp only [children,if_neg h₁,if_neg h₂,List.not_mem_nil] at hq
  · rintro ⟨n,xs,r⟩
    conv_rhs => rw [unitFormulaCode]
    by_cases h₁ : n%4=1
    · simp only [assemble,children,h₁,if_true,true_or,dif_pos,List.map_cons,List.map_nil,List.getD_cons_zero]
    · by_cases h₂ : n%4=2
      · simp only [assemble,children,if_neg h₁,if_pos h₂,dif_pos (Or.inr h₂),List.map_cons,List.map_nil,
          List.getD_cons_zero,List.getD_cons_succ]
      · have h : ¬(n%4=1 ∨ n%4=2) := by tauto
        simp only [assemble,if_neg h₁,if_neg h₂,dif_neg h]

theorem effectiveAlgorithms : Targets.EffectiveAlgorithms := by
  refine ⟨unit_pr,?_⟩
  have hc : Computable (fun p : List Nat×Nat×List Nat×Nat=>UnitEliminationBuildCode.realizedCompileCode p.1 p.2.1) :=
    UnitEliminationBuildCode.Proof.actualUniformSourceCompiler.1.comp Computable.fst (Computable.fst.comp Computable.snd)
  exact Computable.option_map hc (unit_pr.to_comp.comp
    (Computable.snd.pair ((Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))).pair
      (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.fst)))))).to₂
end LogicLineages.OrdinalComparison.Source.ActualHeadGraph.UnitArithmeticFormulaCode.Proof
