import R1Calculator.ArithmeticBounds

/-! Arithmetic laws needed by a constructive proof of Carlson's theorem.
No semantic correctness property is supplied as a hypothesis. -/

namespace R1Calculator

open Ordinal ONote Order

theorem repr_le_principalSum : ∀ {a : ONote}, NF a → a.repr ≤ (principalSum a).repr
  | .zero, _ => le_rfl
  | .oadd e n a, h => by
      rw [principalSum_step_repr n h]
      exact add_le_add (mul_le_mul_left (show ω ^ e.repr ≤
        ω ^ e.repr + (principalSum e).repr from le_self_add) (n : ℕ))
        (repr_le_principalSum h.snd)

/-- Principal sums preserve every strict additive-principal upper bound. -/
theorem principalSum_lt_principal_bound : ∀ {a : ONote}, NF a →
    ∀ {d : Ordinal}, a.repr < ω ^ d → (principalSum a).repr < ω ^ d
  | .zero, _, _, _ => opow_pos _ omega0_pos
  | .oadd e n a, h, d, hb => by
      have hed : e.repr < d := (ONote.NF.below_of_lt' hb h).lt
      have hep : ω ^ e.repr < ω ^ d :=
        (opow_lt_opow_iff_right one_lt_omega0).mpr hed
      have hterm : ω ^ e.repr + (principalSum e).repr < ω ^ d :=
        isPrincipal_add_omega0_opow _ hep
          ((principalSum_repr_lt_omega_opow h.fst).trans hep)
      have hmul : (ω ^ e.repr + (principalSum e).repr) * (n : ℕ) < ω ^ d :=
        mul_lt_omega0_opow hed.pos hterm (natCast_lt_omega0 _)
      have htail : (principalSum a).repr < ω ^ d :=
        principalSum_lt_principal_bound h.snd (h.snd'.repr_lt.trans hep)
      rw [principalSum_step_repr n h]
      exact isPrincipal_add_omega0_opow _ hmul htail

private theorem lastExponent_lt_bound : ∀ {a : ONote} {d : Ordinal},
    NFBelow a d → a ≠ 0 → (lastExponent a).repr < d
  | .zero, _, _, ha => (ha rfl).elim
  | .oadd e n a, d, h, _ => by
      cases a with
      | zero => exact h.lt
      | oadd f m t =>
          exact (lastExponent_lt_bound h.snd (by intro hz; cases hz)).trans h.lt

/-- Endpoints cannot cross a strict additive-principal bound. -/
theorem endpoint_lt_principal_bound {a : ONote} (ha : NF a)
    {d : Ordinal} (hb : a.repr < ω ^ d) : (endpoint a).repr < ω ^ d := by
  by_cases ha0 : a = 0
  · subst a
    simpa using opow_pos d omega0_pos
  haveI : NF a := ha
  haveI : NF (principalSum (lastExponent a)) := principalSum_nf (lastExponent_nf ha)
  rw [endpoint, ONote.repr_add]
  exact isPrincipal_add_omega0_opow _ hb
    ((principalSum_repr_lt_omega_opow (lastExponent_nf ha)).trans
      ((opow_lt_opow_iff_right one_lt_omega0).mpr
        (lastExponent_lt_bound (ONote.NF.below_of_lt' hb ha) ha0)))

private theorem principalSum_monomial_repr (e : ONote) (n : ℕ+) (he : NF e) :
    (principalSum (.oadd e n 0)).repr =
      (ω ^ e.repr + (principalSum e).repr) * (n : ℕ) := by
  simpa using principalSum_step_repr n (he.oadd n NFBelow.zero)

private theorem principalSum_addAux_repr (e : ONote) (n : ℕ+) (a : ONote)
    (he : NF e) (ha : NF a) :
    (principalSum (ONote.addAux e n a)).repr =
      (ω ^ e.repr + (principalSum e).repr) * (n : ℕ) + (principalSum a).repr := by
  cases a with
  | zero => simpa [ONote.addAux] using principalSum_monomial_repr e n he
  | oadd d m t =>
      have hcomp := @ONote.cmp_compares e d he ha.fst
      cases hc : ONote.cmp e d with
      | lt =>
          have hed : e.repr < d.repr := ONote.repr_lt_repr (hcomp.eq_lt.mp hc)
          have hmono : (ONote.oadd e n 0).repr < ω ^ d.repr :=
            (NFBelow.oadd he NFBelow.zero hed).repr_lt
          have hsmall : (ω ^ e.repr + (principalSum e).repr) * (n : ℕ) < ω ^ d.repr := by
            rw [← principalSum_monomial_repr e n he]
            exact principalSum_lt_principal_bound (he.oadd n NFBelow.zero) hmono
          have hbig : ω ^ d.repr ≤ (principalSum (.oadd d m t)).repr :=
            (ONote.omega0_le_oadd d m t).trans (repr_le_principalSum ha)
          simpa only [ONote.addAux, hc] using
            (Ordinal.add_of_omega0_opow_le hsmall hbig).symm
      | eq =>
          have hed : e = d := by
            simpa only [hc, Ordering.compares_eq] using hcomp
          subst d
          simp only [ONote.addAux, hc]
          rw [principalSum_step_repr (n + m) (he.oadd (n + m) ha.snd'),
            principalSum_step_repr m ha]
          simp only [PNat.add_coe, Nat.cast_add, mul_add, add_assoc]
      | gt =>
          have hde : d.repr < e.repr := ONote.repr_lt_repr (hcomp.eq_gt.mp hc)
          simpa only [ONote.addAux, hc] using
            principalSum_step_repr n (he.oadd n (ha.below_of_lt hde))

/-- The correction operator preserves genuine ordinal addition, including
absorption of smaller terms. -/
theorem principalSum_add_repr : ∀ {a b : ONote}, NF a → NF b →
    (principalSum (a + b)).repr = (principalSum a).repr + (principalSum b).repr
  | .zero, _, _, _ => by simp
  | .oadd e n a, b, ha, hb => by
      haveI : NF a := ha.snd
      haveI : NF b := hb
      rw [ONote.oadd_add, principalSum_addAux_repr e n (a + b) ha.fst (ONote.add_nf a b),
        principalSum_add_repr ha.snd hb, principalSum_step_repr n ha]
      exact (add_assoc _ _ _).symm

/-- Strict monotonicity of the correction, proved using the positive remainder
and addition law rather than assumed semantic properties. -/
theorem principalSum_strictMono_repr {a b : ONote} (ha : NF a) (hb : NF b)
    (hab : a.repr < b.repr) : (principalSum a).repr < (principalSum b).repr := by
  haveI : NF a := ha
  haveI : NF b := hb
  have hsum : a + (b - a) = b := by
    apply ONote.repr_inj.mp
    rw [ONote.repr_add, ONote.repr_sub]
    exact Ordinal.add_sub_cancel_of_le hab.le
  have hrem : b - a ≠ 0 := by
    intro hz
    have hr : b.repr = a.repr := by
      rw [← hsum, hz, ONote.repr_add]
      simp
    exact hab.ne hr.symm
  rw [← hsum, principalSum_add_repr ha (ONote.sub_nf b a)]
  exact lt_add_of_pos_right _ (principalSum_repr_pos (ONote.sub_nf b a) hrem)

/-- The next principal block above a strict cutoff cannot pass a point
divisible by that block. -/
theorem add_principal_le_of_dvd {cut r d : Ordinal} (hcut : cut < r)
    (hdvd : ω ^ d ∣ r) : cut + ω ^ d ≤ r := by
  obtain ⟨q, rfl⟩ := hdvd
  obtain ⟨j, hj, t, ht, hcut⟩ := Ordinal.lt_mul_iff.mp hcut
  rw [hcut, add_assoc, (isPrincipal_add_omega0_opow d).add_eq_right ht,
    ← mul_add_one]
  exact mul_le_mul_right (add_one_le_of_lt hj) _

/-- A normal notation is divisible by its final monomial. -/
theorem lastExponent_opow_dvd : ∀ {a : ONote}, NF a →
    ω ^ (lastExponent a).repr ∣ a.repr
  | .zero, _ => by simp
  | .oadd e n a, h => by
      cases a with
      | zero =>
          change ω ^ e.repr ∣ ω ^ e.repr * (n : ℕ) + 0
          simp only [add_zero]
          exact dvd_mul_right _ _
      | oadd d m t =>
          have hlast : (lastExponent (.oadd d m t)).repr < e.repr :=
            lastExponent_lt_bound h.snd' (by intro hz; cases hz)
          change ω ^ (lastExponent (.oadd d m t)).repr ∣
            ω ^ e.repr * (n : ℕ) + (ONote.oadd d m t).repr
          exact dvd_add (dvd_mul_of_dvd_left (opow_dvd_opow ω hlast.le) _)
            (lastExponent_opow_dvd h.snd)

/-- Rounding lemma for the first point of a greedy finite-forest copy. -/
theorem principal_rounding {a : ONote} (ha : NF a) {cut d : Ordinal}
    (hcut : cut < a.repr) (hd : d ≤ (lastExponent a).repr) :
    cut + ω ^ d ≤ a.repr :=
  add_principal_le_of_dvd hcut
    ((opow_dvd_opow ω hd).trans (lastExponent_opow_dvd ha))

/-- Endpoints of points strictly below a finite multiple of a principal
ordinal remain strictly below that multiple. -/
theorem endpoint_lt_monomial_bound {a : ONote} (ha : NF a)
    {d : Ordinal} {n : ℕ} (hb : a.repr < ω ^ d * n) :
    (endpoint a).repr < ω ^ d * n := by
  by_cases ha0 : a = 0
  · subst a
    exact hb
  have hpow : ω ^ d * n < ω ^ Order.succ d :=
    opow_mul_lt_opow (natCast_lt_omega0 n) (Order.lt_succ d)
  have hlast : (lastExponent a).repr ≤ d :=
    Order.lt_succ_iff.mp
      (lastExponent_lt_bound (ONote.NF.below_of_lt' (hb.trans hpow) ha) ha0)
  have hdvd : ω ^ (lastExponent a).repr ∣ ω ^ d * n :=
    dvd_mul_of_dvd_left (opow_dvd_opow ω hlast) _
  haveI : NF a := ha
  haveI : NF (principalSum (lastExponent a)) := principalSum_nf (lastExponent_nf ha)
  rw [endpoint, ONote.repr_add]
  exact ((add_lt_add_iff_left a.repr).mpr
    (principalSum_repr_lt_omega_opow (lastExponent_nf ha))).trans_le
      (add_principal_le_of_dvd hb hdvd)

/-- Adding a sufficiently small tail stays below a final principal block. -/
theorem add_small_lt_final_block {cut base d tail : Ordinal}
    (hcut : cut < base + ω ^ d) (htail : tail < ω ^ d) :
    cut + tail < base + ω ^ d := by
  obtain ⟨t, ht, hbound⟩ := (Ordinal.lt_add_iff (opow_ne_zero _ omega0_ne_zero)).mp hcut
  calc
    cut + tail ≤ (base + t) + tail := add_le_add_left hbound tail
    _ = base + (t + tail) := add_assoc _ _ _
    _ < base + ω ^ d :=
      (add_lt_add_iff_left base).mpr (isPrincipal_add_omega0_opow d ht htail)

theorem principalSum_le_iff {a b : ONote} (ha : NF a) (hb : NF b) :
    (principalSum a).repr ≤ (principalSum b).repr ↔ a.repr ≤ b.repr := by
  constructor
  · intro h
    by_contra hn
    exact (not_le_of_gt (principalSum_strictMono_repr hb ha (lt_of_not_ge hn))) h
  · intro h
    rcases lt_or_eq_of_le h with h | h
    · exact (principalSum_strictMono_repr ha hb h).le
    · haveI : NF a := ha
      haveI : NF b := hb
      exact (congrArg (fun c => (principalSum c).repr) (ONote.repr_inj.mp h)).le

theorem principalSum_lt_iff {a b : ONote} (ha : NF a) (hb : NF b) :
    (principalSum a).repr < (principalSum b).repr ↔ a.repr < b.repr := by
  rw [lt_iff_not_ge, lt_iff_not_ge, principalSum_le_iff hb ha]

#print axioms principalSum_add_repr
#print axioms principalSum_strictMono_repr
#print axioms endpoint_lt_principal_bound
#print axioms principal_rounding
#print axioms endpoint_lt_monomial_bound

end R1Calculator
