module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.MaskRestrictionCodeTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.MaskRestrictionCode.Proof
open SeededInputCode (variableCode addCode negateCode shiftCode zeroCode)
attribute [local irreducible] Nat.sqrt Nat.unpair

private theorem variable_pr : Primrec variableCode :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 6) Primrec.id) (Primrec.const 1)
private theorem add_pr : Primrec₂ addCode :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 6) Primrec₂.natPair) (Primrec.const 2)
private theorem negate_pr : Primrec negateCode :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 6) Primrec.id) (Primrec.const 3)
private theorem shift_pr : Primrec shiftCode :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 6) Primrec.id) (Primrec.const 4)

theorem extend_masks_pr : Primrec extendMasks := by
  have hp : Primrec (fun z : List Bool => [false :: z, true :: z]) :=
    Primrec.list_cons.comp (Primrec.list_cons.comp (Primrec.const false) Primrec.id)
      (Primrec.list_cons.comp (Primrec.list_cons.comp (Primrec.const true) Primrec.id)
        (Primrec.const []))
  exact Primrec.list_flatMap Primrec.id (hp.comp Primrec.snd).to₂

theorem masks_pr : Primrec masksCode := by
  apply (Primrec.nat_iterate Primrec.id (Primrec.const ([[]] : List (List Bool)))
    (extend_masks_pr.comp Primrec.snd).to₂).of_eq
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      change (extendMasks^[n+1]) [[]] = masksCode (n+1)
      change (extendMasks^[n]) [[]] = masksCode n at ih
      rw [Function.iterate_succ_apply', ih]
      rfl

theorem restrict_pr : Primrec₂ restrictCode := by
  let children : List Bool × Nat → List (List Bool × Nat) := fun s =>
    if s.2 % 6 = 2 then [(s.1, (s.2 / 6).unpair.1), (s.1, (s.2 / 6).unpair.2)]
    else if s.2 % 6 = 3 ∨ s.2 % 6 = 4 then [(s.1, s.2 / 6)] else []
  let base : List Bool × Nat → Nat := fun s =>
    if s.2 % 6 = 1 then
      if s.1.getD (s.2 / 6) false then variableCode (s.2 / 6) else zeroCode
    else 0
  let assemble : (List Bool × Nat) → List Nat → Option Nat := fun s rs => some
    (if s.2 % 6 = 2 then addCode (rs.getD 0 0) (rs.getD 1 0)
    else if s.2 % 6 = 3 then negateCode (rs.getD 0 0)
    else if s.2 % 6 = 4 then shiftCode (rs.getD 0 0)
    else base s)
  have htag : Primrec (fun s : List Bool × Nat => s.2 % 6) :=
    Primrec.nat_mod.comp Primrec.snd (Primrec.const 6)
  have hpay : Primrec (fun s : List Bool × Nat => s.2 / 6) :=
    Primrec.nat_div.comp Primrec.snd (Primrec.const 6)
  have hl := Primrec.fst.comp (Primrec.unpair.comp hpay)
  have hr := Primrec.snd.comp (Primrec.unpair.comp hpay)
  have htag_eq (k : Nat) : PrimrecPred (fun s : List Bool × Nat => s.2 % 6 = k) :=
    Primrec.eq.comp htag (Primrec.const k)
  have hc : Primrec children := Primrec.ite (htag_eq 2)
    (Primrec.list_cons.comp (Primrec.fst.pair hl)
      (Primrec.list_cons.comp (Primrec.fst.pair hr) (Primrec.const [])))
    (Primrec.ite ((htag_eq 3).or (htag_eq 4))
      (Primrec.list_cons.comp (Primrec.fst.pair hpay) (Primrec.const [])) (Primrec.const []))
  have hbit := (Primrec.list_getD false).comp Primrec.fst hpay
  have hb : Primrec base := Primrec.ite (htag_eq 1)
    (Primrec.ite (Primrec.eq.comp hbit (Primrec.const true))
      (variable_pr.comp hpay) (Primrec.const zeroCode)) (Primrec.const 0)
  have ha : Primrec₂ assemble := by
    have hg (k : Nat) : Primrec (fun p : (List Bool × Nat) × List Nat => p.2.getD k 0) :=
      (Primrec.list_getD (0 : Nat)).comp Primrec.snd (Primrec.const k)
    exact Primrec.option_some.comp (Primrec.ite ((htag_eq 2).comp Primrec.fst)
      (add_pr.comp (hg 0) (hg 1))
      (Primrec.ite ((htag_eq 3).comp Primrec.fst) (negate_pr.comp (hg 0))
      (Primrec.ite ((htag_eq 4).comp Primrec.fst) (shift_pr.comp (hg 0)) (hb.comp Primrec.fst))))
  apply Primrec.nat_omega_rec' (fun s : List Bool × Nat => restrictCode s.1 s.2) Primrec.snd hc ha
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
    conv_rhs => rw [restrictCode]
    have htags : s.2 % 6 = 0 ∨ s.2 % 6 = 1 ∨ s.2 % 6 = 2 ∨
        s.2 % 6 = 3 ∨ s.2 % 6 = 4 ∨ s.2 % 6 = 5 := by omega
    rcases htags with h | h | h | h | h | h <;> simp [children, assemble, base, h]

theorem restrict_rows_pr : Primrec₂ restrictRows :=
  Primrec.list_map Primrec.snd
    (restrict_pr.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂

theorem numericalPrograms : Targets.NumericalPrograms :=
  ⟨extend_masks_pr, masks_pr, restrict_pr, restrict_rows_pr⟩

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.MaskRestrictionCode.Proof
