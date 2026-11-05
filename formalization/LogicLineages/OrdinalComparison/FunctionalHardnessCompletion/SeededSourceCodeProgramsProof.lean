module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.SeededSourceCodeTargets
public import LogicLineages.OrdinalComparison.ContextInsertionCodePrimitiveProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.SeededSourceCode.Proof
attribute [local irreducible] Nat.sqrt Nat.unpair unitCode seedCode

private theorem app_pr : Primrec₂ appCode :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 8) Primrec₂.natPair) (Primrec.const 5)
private theorem lam_pr : Primrec₂ lamCode :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 8) Primrec₂.natPair) (Primrec.const 6)
private theorem weaken_pr : Primrec weakenCode :=
  ContextInsertionCode.Proof.primitiveRecursiveAlgorithms.1.comp
    ((Primrec.const 0).pair ((Primrec.const 1).pair Primrec.id))

theorem combine_pr : Primrec₂ combineCode :=
  app_pr.comp
    (lam_pr.comp (Primrec.const (SyntaxCode.typeCode (.arrow .ground FunctionalDetector.unary)))
      (weaken_pr.comp Primrec.fst))
    (lam_pr.comp (Primrec.const 0) (weaken_pr.comp Primrec.snd))

theorem project_pr : Primrec₂ projectCode :=
  app_pr.comp (lam_pr.comp (Primrec.const (SyntaxCode.typeCode FunctionalDetector.unary))
    (weaken_pr.comp Primrec.fst)) Primrec.snd

theorem omega_pr : Primrec omegaCode :=
  app_pr.comp (Primrec.const (appCode 4 1)) (lam_pr.comp (Primrec.const 0) weaken_pr)

theorem join_pr : Primrec₂ joinCode :=
  (combine_pr.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)).pair
    (combine_pr.comp (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))

private theorem eight_pr : Primrec eightCode :=
  (combine_pr.comp Primrec.fst (Primrec.const identityCode)).pair
    (combine_pr.comp Primrec.snd (Primrec.const identityCode))
private theorem sixteen_pr : Primrec sixteenCode := join_pr.comp Primrec.id Primrec.id

private theorem iterate_pr {α : Type} [Primcodable α] (f : α → α) (hf : Primrec f) :
    Primrec (fun p : Nat × α => (f^[p.1]) p.2) :=
  Primrec.nat_iterate Primrec.fst Primrec.snd (hf.comp Primrec.snd).to₂

theorem pad_pr : Primrec₂ padCode := by
  have hm : Primrec (fun p : Nat × PairCode => p.1 % 3) :=
    Primrec.nat_mod.comp Primrec.fst (Primrec.const 3)
  have hk : Primrec (fun p : Nat × PairCode => p.1 / 3 + (2 - p.1 % 3)) :=
    Primrec.nat_add.comp (Primrec.nat_div.comp Primrec.fst (Primrec.const 3))
      (Primrec.nat_sub.comp (Primrec.const 2) hm)
  exact (iterate_pr sixteenCode sixteen_pr).comp
    (hm.pair ((iterate_pr eightCode eight_pr).comp (hk.pair Primrec.snd)))

theorem variable_pr : Primrec variableCode := by
  have hv : Primrec (fun i : Nat => projectCode (8 * i) identityCode) :=
    project_pr.comp (Primrec.nat_mul.comp (Primrec.const 8) Primrec.id) (Primrec.const identityCode)
  have hp : Primrec (fun i : Nat =>
      (projectCode (8 * i) identityCode, projectCode identityCode identityCode)) :=
    hv.pair (Primrec.const (projectCode identityCode identityCode))
  exact join_pr.comp ((iterate_pr eightCode eight_pr).comp ((Primrec.const 3).pair hp))
    (Primrec.const unitCode)

private theorem neg_step_pr : Primrec negStep :=
  ((Primrec.snd.comp Primrec.fst).pair (Primrec.fst.comp Primrec.fst)).pair Primrec.snd
private theorem omega_step_pr : Primrec omegaStep :=
  ((omega_pr.comp (Primrec.fst.comp Primrec.fst)).pair
    (omega_pr.comp (Primrec.snd.comp Primrec.fst))).pair (Primrec.succ.comp Primrec.snd)
private theorem add_step_pr : Primrec₂ addStep := by
  have hs : Primrec (fun p : State × State => p.1.2) := Primrec.snd.comp Primrec.fst
  have ht : Primrec (fun p : State × State => p.2.2) := Primrec.snd.comp Primrec.snd
  have hk : Primrec (fun p : State × State => max p.1.2 p.2.2) := Primrec.nat_max.comp hs ht
  have hl : Primrec (fun p : State × State => padCode (max p.1.2 p.2.2 - p.1.2) p.1.1) :=
    pad_pr.comp (Primrec.nat_sub.comp hk hs) (Primrec.fst.comp Primrec.fst)
  have hr : Primrec (fun p : State × State => padCode (max p.1.2 p.2.2 - p.2.2) p.2.1) :=
    pad_pr.comp (Primrec.nat_sub.comp hk ht) (Primrec.fst.comp Primrec.snd)
  exact (join_pr.comp hl hr).pair (Primrec.nat_add.comp hk (Primrec.const 9))

theorem compiler_pr : Primrec₂ compilerCode := by
  let children : Nat × Nat → List (Nat × Nat) := fun s =>
    if s.2 % 6 = 2 then [(s.1, (s.2 / 6).unpair.1), (s.1, (s.2 / 6).unpair.2)]
    else if s.2 % 6 = 3 ∨ s.2 % 6 = 4 then [(s.1, s.2 / 6)] else []
  let base : Nat × Nat → State := fun s =>
    if s.2 % 6 = 1 then
      if s.2 / 6 < s.1 then (variableCode (s.2 / 6), 15) else (seedCode, 12)
    else (unitCode, 12)
  let assemble : (Nat × Nat) → List State → Option State := fun s rs => some
    (if s.2 % 6 = 2 then addStep (rs.getD 0 (unitCode, 12)) (rs.getD 1 (unitCode, 12))
    else if s.2 % 6 = 3 then negStep (rs.getD 0 (unitCode, 12))
    else if s.2 % 6 = 4 then omegaStep (rs.getD 0 (unitCode, 12))
    else base s)
  have htag : Primrec (fun s : Nat × Nat => s.2 % 6) :=
    Primrec.nat_mod.comp Primrec.snd (Primrec.const 6)
  have hpay : Primrec (fun s : Nat × Nat => s.2 / 6) :=
    Primrec.nat_div.comp Primrec.snd (Primrec.const 6)
  have hl := Primrec.fst.comp (Primrec.unpair.comp hpay)
  have hr := Primrec.snd.comp (Primrec.unpair.comp hpay)
  have htag_eq (k : Nat) : PrimrecPred (fun s : Nat × Nat => s.2 % 6 = k) :=
    Primrec.eq.comp htag (Primrec.const k)
  have hc : Primrec children := Primrec.ite (htag_eq 2)
    (Primrec.list_cons.comp (Primrec.fst.pair hl)
      (Primrec.list_cons.comp (Primrec.fst.pair hr) (Primrec.const [])))
    (Primrec.ite ((htag_eq 3).or (htag_eq 4))
      (Primrec.list_cons.comp (Primrec.fst.pair hpay) (Primrec.const [])) (Primrec.const []))
  have hb : Primrec base := Primrec.ite (htag_eq 1)
    (Primrec.ite (Primrec.nat_lt.comp hpay Primrec.fst)
      ((variable_pr.comp hpay).pair (Primrec.const 15)) (Primrec.const (seedCode, 12)))
    (Primrec.const (unitCode, 12))
  have ha : Primrec₂ assemble := by
    have hg (k : Nat) : Primrec (fun p : (Nat × Nat) × List State => p.2.getD k (unitCode, 12)) :=
      (Primrec.list_getD ((unitCode, 12) : State)).comp Primrec.snd (Primrec.const k)
    exact Primrec.option_some.comp (Primrec.ite ((htag_eq 2).comp Primrec.fst)
      (add_step_pr.comp (hg 0) (hg 1))
      (Primrec.ite ((htag_eq 3).comp Primrec.fst) (neg_step_pr.comp (hg 0))
      (Primrec.ite ((htag_eq 4).comp Primrec.fst) (omega_step_pr.comp (hg 0)) (hb.comp Primrec.fst))))
  apply Primrec.nat_omega_rec' (fun s : Nat × Nat => compilerCode s.1 s.2) Primrec.snd hc ha
  · intro s t ht
    by_cases h2 : s.2 % 6 = 2
    · have hd : s.2 / 6 < s.2 := Nat.div_lt_self (by omega) (by decide)
      simp only [children, if_pos h2, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · exact (Nat.unpair_left_le _).trans_lt hd
      · exact (Nat.unpair_right_le _).trans_lt hd
    · by_cases h34 : s.2 % 6 = 3 ∨ s.2 % 6 = 4
      · have hd : s.2 / 6 < s.2 := Nat.div_lt_self (by omega) (by decide)
        simp only [children, if_neg h2, if_pos h34, List.mem_singleton] at ht
        subst t
        exact hd
      · simp [children, h2, h34] at ht
  · intro s
    conv_rhs => rw [compilerCode]
    have htags : s.2 % 6 = 0 ∨ s.2 % 6 = 1 ∨ s.2 % 6 = 2 ∨
        s.2 % 6 = 3 ∨ s.2 % 6 = 4 ∨ s.2 % 6 = 5 := by omega
    rcases htags with h | h | h | h | h | h <;> simp [children, assemble, base, h]

theorem numericalPrograms : Targets.NumericalPrograms :=
  ⟨combine_pr, project_pr, omega_pr, join_pr, pad_pr, variable_pr, compiler_pr⟩

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.SeededSourceCode.Proof
