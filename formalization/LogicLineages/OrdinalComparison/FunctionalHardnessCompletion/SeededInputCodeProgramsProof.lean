module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.SeededInputCodeTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.IntegerAlgorithmsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.SeededInputCode.Proof
attribute [local irreducible] Nat.sqrt Nat.unpair

private theorem variable_pr : Primrec variableCode :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 6) Primrec.id) (Primrec.const 1)
private theorem add_pr : Primrec₂ addCode :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 6) Primrec₂.natPair) (Primrec.const 2)
private theorem negate_pr : Primrec negateCode :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 6) Primrec.id) (Primrec.const 3)
private theorem shift_pr : Primrec shiftCode :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 6) Primrec.id) (Primrec.const 4)
private theorem repeat_pr : Primrec₂ repeatCode :=
  Primrec.nat_iterate Primrec.snd (Primrec.const zeroCode)
    (add_pr.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂
private theorem shift_iterate_pr : Primrec (fun p : Nat × Nat => (shiftCode^[p.1]) p.2) :=
  Primrec.nat_iterate Primrec.fst Primrec.snd (shift_pr.comp Primrec.snd).to₂

private theorem negative_pr : PrimrecPred (fun z : Int => z < 0) :=
  (Primrec.eq.comp LayeredComparison.IntegerAlgorithms.Proof.sign_primitive
    (Primrec.const (-1 : Int))).of_eq (fun _ => Int.sign_eq_neg_one_iff_neg)

theorem expand_pr : Primrec expandMonomial := by
  have hbase : Primrec (fun m : MonomialCode =>
      match m.2.2 with | none => 0 | some i => variableCode i) := by
    apply (Primrec.option_casesOn (Primrec.snd.comp Primrec.snd) (Primrec.const 0)
      (variable_pr.comp Primrec.snd).to₂).of_eq
    intro m
    cases m.2.2 <;> rfl
  have hshift : Primrec (fun m : MonomialCode =>
      (shiftCode^[m.2.1]) (match m.2.2 with | none => 0 | some i => variableCode i)) :=
    shift_iterate_pr.comp ((Primrec.fst.comp Primrec.snd).pair hbase)
  have hbody := repeat_pr.comp hshift
    (LayeredComparison.IntegerAlgorithms.Proof.abs_primitive.comp Primrec.fst)
  exact Primrec.ite (negative_pr.comp Primrec.fst) (negate_pr.comp hbody) hbody

theorem valid_pr : Primrec₂ validMonomial := by
  have hsome : Primrec (fun p : (Nat × MonomialCode) × Nat => decide (p.2 < p.1.1)) :=
    (Primrec.nat_lt.comp Primrec.snd (Primrec.fst.comp Primrec.fst)).decide
  apply (Primrec.option_casesOn (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
    (Primrec.const true) hsome.to₂).of_eq
  intro p
  unfold validMonomial
  cases p.2.2.2 <;> rfl

theorem monomial_pr : Primrec₂ monomialCode :=
  Primrec.ite (Primrec.eq.comp valid_pr (Primrec.const true))
    (Primrec.option_some.comp (expand_pr.comp Primrec.snd)) (Primrec.const none)

theorem row_pr : Primrec₂ rowCode := by
  have hm : Primrec (fun p : (Nat × List MonomialCode) × (MonomialCode × Nat) =>
      monomialCode p.1.1 p.2.1) :=
    monomial_pr.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)
  have ha : Primrec (fun p : (Nat × List MonomialCode) × (MonomialCode × Nat) => p.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hs : Primrec (fun p : (Nat × List MonomialCode) × (MonomialCode × Nat) =>
      match monomialCode p.1.1 p.2.1 with | none => p.2.2 | some b => addCode b p.2.2) := by
    apply (Primrec.option_casesOn hm ha (add_pr.comp Primrec.snd (ha.comp Primrec.fst)).to₂).of_eq
    intro p
    cases monomialCode p.1.1 p.2.1 <;> rfl
  exact Primrec.list_foldr Primrec.snd (Primrec.const zeroCode) hs.to₂

theorem subtract_seed_pr : Primrec₂ subtractSeedCode := by
  let children : Nat × Nat → List (Nat × Nat) := fun s =>
    if s.2 % 6 = 2 then [(s.1, (s.2 / 6).unpair.1), (s.1, (s.2 / 6).unpair.2)]
    else if s.2 % 6 = 3 ∨ s.2 % 6 = 4 then [(s.1, s.2 / 6)] else []
  let base : Nat × Nat → Nat := fun s =>
    if s.2 % 6 = 1 then addCode (variableCode (s.2 / 6)) (negateCode (variableCode s.1)) else 0
  let assemble : (Nat × Nat) → List Nat → Option Nat := fun s rs => some
    (if s.2 % 6 = 2 then addCode (rs.getD 0 0) (rs.getD 1 0)
    else if s.2 % 6 = 3 then negateCode (rs.getD 0 0)
    else if s.2 % 6 = 4 then shiftCode (rs.getD 0 0)
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
    (add_pr.comp (variable_pr.comp hpay) (negate_pr.comp (variable_pr.comp Primrec.fst)))
    (Primrec.const 0)
  have ha : Primrec₂ assemble := by
    have hg (k : Nat) : Primrec (fun p : (Nat × Nat) × List Nat => p.2.getD k 0) :=
      (Primrec.list_getD (0 : Nat)).comp Primrec.snd (Primrec.const k)
    exact Primrec.option_some.comp (Primrec.ite ((htag_eq 2).comp Primrec.fst)
      (add_pr.comp (hg 0) (hg 1))
      (Primrec.ite ((htag_eq 3).comp Primrec.fst) (negate_pr.comp (hg 0))
      (Primrec.ite ((htag_eq 4).comp Primrec.fst) (shift_pr.comp (hg 0)) (hb.comp Primrec.fst))))
  apply Primrec.nat_omega_rec' (fun s : Nat × Nat => subtractSeedCode s.1 s.2) Primrec.snd hc ha
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
    conv_rhs => rw [subtractSeedCode]
    have htags : s.2 % 6 = 0 ∨ s.2 % 6 = 1 ∨ s.2 % 6 = 2 ∨
        s.2 % 6 = 3 ∨ s.2 % 6 = 4 ∨ s.2 % 6 = 5 := by omega
    rcases htags with h | h | h | h | h | h <;> simp [children, assemble, base, h]

theorem input_pr : Primrec inputCode :=
  Primrec.list_map Primrec.snd (row_pr.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂

theorem seeded_input_pr : Primrec seededInputCode :=
  Primrec.list_map input_pr
    (subtract_seed_pr.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂

theorem numericalPrograms : Targets.NumericalPrograms :=
  ⟨expand_pr, valid_pr, monomial_pr, row_pr, subtract_seed_pr, input_pr, seeded_input_pr⟩

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.SeededInputCode.Proof
