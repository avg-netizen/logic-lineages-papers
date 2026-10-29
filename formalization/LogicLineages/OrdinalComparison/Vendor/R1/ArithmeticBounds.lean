module
public import LogicLineages.OrdinalComparison.Vendor.R1.Ordinal

@[expose] public section

/-!
# Cofinal room in the compressed endpoint recursion

These arithmetic bounds are proved directly on hereditary Cantor normal forms.
They are useful in a constructive proof of Carlson's semantic characterization;
they do not assume that characterization or themselves establish elementarity.
-/

namespace LogicLineages.OrdinalComparison.Vendor.R1

open Ordinal ONote

/-- Every normal finite hereditary notation is strictly below its own omega power.
This uses the finite syntax, rather than an assumed epsilon-zero range theorem. -/
theorem repr_lt_omega_opow : ∀ {a : ONote}, NF a → a.repr < ω ^ a.repr
  | .zero, _ => by simp
  | .oadd e n a, h => by
      have he : e.repr < (ONote.oadd e n a).repr :=
        (repr_lt_omega_opow h.fst).trans_le (ONote.omega0_le_oadd e n a)
      exact (h.below_of_lt he).repr_lt

/-- Denotation of one compressed principal-sum step, in its original order. -/
theorem principalSum_step_repr {e a : ONote} (n : ℕ+)
    (h : NF (ONote.oadd e n a)) :
    (principalSum (ONote.oadd e n a)).repr =
      (ω ^ e.repr + (principalSum e).repr) * (n : ℕ) + (principalSum a).repr := by
  haveI : NF e := h.fst
  haveI : NF (principalSum e) := principalSum_nf h.fst
  haveI : NF (principalSum a) := principalSum_nf h.snd
  simp only [principalSum, ONote.mulNat_eq_mul, ONote.repr_add,
    ONote.repr_mul, ONote.repr_ofNat, ONote.repr, PNat.one_coe, Nat.cast_one, mul_one, add_zero]

/-- The principal-sum correction fits strictly below the input's omega power. -/
theorem principalSum_repr_lt_omega_opow :
    ∀ {a : ONote}, NF a → (principalSum a).repr < ω ^ a.repr
  | .zero, _ => by simp
  | .oadd e n a, h => by
      have he : e.repr < (ONote.oadd e n a).repr :=
        (repr_lt_omega_opow h.fst).trans_le (ONote.omega0_le_oadd e n a)
      have ha : a.repr < (ONote.oadd e n a).repr :=
        h.snd'.repr_lt.trans_le (ONote.omega0_le_oadd e n a)
      have hpow : ω ^ e.repr < ω ^ (ONote.oadd e n a).repr :=
        (opow_lt_opow_iff_right one_lt_omega0).mpr he
      have hhead : ω ^ e.repr + (principalSum e).repr < ω ^ (ONote.oadd e n a).repr :=
        isPrincipal_add_omega0_opow _ hpow
          ((principalSum_repr_lt_omega_opow h.fst).trans hpow)
      have hmul : (ω ^ e.repr + (principalSum e).repr) * (n : ℕ) <
          ω ^ (ONote.oadd e n a).repr :=
        mul_lt_omega0_opow (ONote.oadd_pos e n a) hhead (natCast_lt_omega0 _)
      have htail : (principalSum a).repr < ω ^ (ONote.oadd e n a).repr :=
        (principalSum_repr_lt_omega_opow h.snd).trans
          ((opow_lt_opow_iff_right one_lt_omega0).mpr ha)
      rw [principalSum_step_repr n h]
      exact isPrincipal_add_omega0_opow _ hmul htail

/-- A nonzero input has a genuinely positive principal-sum correction. -/
theorem principalSum_repr_pos {a : ONote} (h : NF a) (ha : a ≠ 0) :
    0 < (principalSum a).repr := by
  cases a with
  | zero => exact (ha rfl).elim
  | oadd e n a =>
      rw [principalSum_step_repr n h]
      apply lt_of_lt_of_le (b := (ω ^ e.repr + (principalSum e).repr) * (n : ℕ))
      · exact mul_pos ((opow_pos e.repr omega0_pos).trans_le le_self_add)
          (Nat.cast_pos'.2 n.pos)
      · exact le_self_add

/-- The final exponent is genuinely smaller than any nonzero normal input. -/
theorem lastExponent_repr_lt : ∀ {a : ONote}, NF a → a ≠ 0 →
    (lastExponent a).repr < a.repr
  | .zero, _, ha => (ha rfl).elim
  | .oadd e n a, h, _ => by
      have he : e.repr < (ONote.oadd e n a).repr :=
        (repr_lt_omega_opow h.fst).trans_le (ONote.omega0_le_oadd e n a)
      cases a with
      | zero => exact he
      | oadd d m t =>
          exact (lastExponent_repr_lt h.snd (by intro h; cases h)).trans
            (h.snd'.repr_lt.trans_le (ONote.omega0_le_oadd e n (.oadd d m t)))

/-- The entire computed endpoint also fits below the input's omega power. -/
theorem endpoint_repr_lt_omega_opow {a : ONote} (h : NF a) :
    (endpoint a).repr < ω ^ a.repr := by
  by_cases ha : a = 0
  · subst a
    simp
  haveI : NF a := h
  haveI : NF (principalSum (lastExponent a)) :=
    principalSum_nf (lastExponent_nf h)
  rw [endpoint, ONote.repr_add]
  exact isPrincipal_add_omega0_opow _ (repr_lt_omega_opow h)
    ((principalSum_repr_lt_omega_opow (lastExponent_nf h)).trans
      ((opow_lt_opow_iff_right one_lt_omega0).mpr (lastExponent_repr_lt h ha)))

private theorem addAux_ne_zero (e : ONote) (n : ℕ+) (a : ONote) :
    ONote.addAux e n a ≠ 0 := by
  cases a with
  | zero => simp [ONote.addAux]
  | oadd d m t =>
      cases h : ONote.cmp e d <;> simp [ONote.addAux, h]

private theorem add_ne_zero_right (a b : ONote) (hb : b ≠ 0) : a + b ≠ 0 := by
  cases a with
  | zero => exact hb
  | oadd e n t => exact addAux_ne_zero e n (t + b)

private theorem lastExponent_addAux {e a : ONote} (n : ℕ+)
    (he : NF e) (ha : NF a) (hzero : a ≠ 0) :
    lastExponent (ONote.addAux e n a) = lastExponent a := by
  cases a with
  | zero => exact (hzero rfl).elim
  | oadd d m t =>
      cases hc : ONote.cmp e d with
      | lt => simp only [ONote.addAux, hc]
      | eq =>
          have hed : e = d := by
            have hcmp := @ONote.cmp_compares e d he ha.fst
            simpa only [hc, Ordering.compares_eq] using hcmp
          subst d
          simp only [ONote.addAux, hc]
          cases t <;> rfl
      | gt =>
          simp only [ONote.addAux, hc]
          rfl

/-- A nonzero right summand supplies the final exponent of ordinal addition. -/
theorem lastExponent_add : ∀ {a b : ONote}, NF a → NF b → b ≠ 0 →
    lastExponent (a + b) = lastExponent b
  | .zero, _, _, _, _ => rfl
  | .oadd e n a, b, ha, hb, hb0 => by
      haveI : NF a := ha.snd
      haveI : NF b := hb
      rw [ONote.oadd_add,
        lastExponent_addAux n ha.fst (ONote.add_nf a b) (add_ne_zero_right a b hb0)]
      exact lastExponent_add ha.snd hb hb0

/-- Endpoint arithmetic commutes with an additive prefix when the tail is
nonzero. This is arithmetic translation, without a semantic resemblance premise. -/
theorem endpoint_add_right_repr {a b : ONote} (ha : NF a) (hb : NF b) (hb0 : b ≠ 0) :
    (endpoint (a + b)).repr = a.repr + (endpoint b).repr := by
  haveI : NF a := ha
  haveI : NF b := hb
  haveI : NF (principalSum (lastExponent b)) := principalSum_nf (lastExponent_nf hb)
  simp only [endpoint, lastExponent_add ha hb hb0, ONote.repr_add]
  exact add_assoc _ _ _

#print axioms principalSum_repr_lt_omega_opow
#print axioms principalSum_repr_pos
#print axioms endpoint_add_right_repr

end LogicLineages.OrdinalComparison.Vendor.R1
