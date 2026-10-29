module
public import LogicLineages.OrdinalComparison.Vendor.R1.ArithmeticBounds
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-! The expanded hereditary-monomial norm and its sharp triangular endpoint
bound. Coefficients are charged in unary; this is not a binary-size or time bound. -/

namespace LogicLineages.OrdinalComparison.Vendor.R1

open ONote

def treeWeight : ONote → Nat
  | .zero => 0
  | .oadd e n a => (n : Nat) * (1 + treeWeight e) + treeWeight a

def triangular : Nat → Nat
  | 0 => 0
  | n + 1 => triangular n + (n + 1)

theorem triangular_superadd (n m : Nat) :
    triangular n + triangular m ≤ triangular (n + m) := by
  induction m with
  | zero => simp [triangular]
  | succ m ih =>
      change triangular n + (triangular m + (m + 1)) ≤
        triangular (n + m) + (n + m + 1)
      omega

theorem triangular_mono {n m : Nat} (h : n ≤ m) : triangular n ≤ triangular m := by
  induction h with
  | refl => exact le_rfl
  | @step m h ih => exact ih.trans (by simp only [triangular]; omega)

theorem triangular_mul (n m : Nat) : n * triangular m ≤ triangular (n * m) := by
  induction n with
  | zero => simp [triangular]
  | succ n ih =>
      simpa only [Nat.succ_mul] using
        (Nat.add_le_add_right ih (triangular m)).trans (triangular_superadd (n * m) m)

theorem two_mul_triangular (n : Nat) : 2 * triangular n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [triangular, Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul] at ih ⊢
      omega

theorem triangular_formula (n : Nat) : triangular n = n * (n + 1) / 2 := by
  have h := two_mul_triangular n
  omega

private theorem addAux_treeWeight_le (e : ONote) (n : ℕ+) (a : ONote)
    (he : NF e) (ha : NF a) :
    treeWeight (ONote.addAux e n a) ≤ (n : Nat) * (1 + treeWeight e) + treeWeight a := by
  cases a with
  | zero => simp [ONote.addAux, treeWeight]
  | oadd d m t =>
      cases hc : ONote.cmp e d with
      | lt => simp only [ONote.addAux, hc]; exact Nat.le_add_left _ _
      | eq =>
          have hed : e = d := by
            have h := @ONote.cmp_compares e d he ha.fst
            simpa only [hc, Ordering.compares_eq] using h
          subst d
          simp only [ONote.addAux, hc, treeWeight, PNat.add_coe, Nat.add_mul]
          omega
      | gt => simp only [ONote.addAux, hc, treeWeight]; exact le_rfl

theorem treeWeight_add_le : ∀ {a b : ONote}, NF a → NF b →
    treeWeight (a + b) ≤ treeWeight a + treeWeight b
  | .zero, _, _, _ => by simp [treeWeight]
  | .oadd e n a, b, ha, hb => by
      haveI : NF a := ha.snd
      haveI : NF b := hb
      rw [ONote.oadd_add]
      have h := addAux_treeWeight_le e n (a + b) ha.fst (ONote.add_nf a b)
      have ih := treeWeight_add_le ha.snd hb
      simp only [treeWeight]
      omega

theorem treeWeight_mulNat_le (a : ONote) (ha : NF a) (n : Nat) :
    treeWeight (ONote.mulNat a n) ≤ n * treeWeight a := by
  haveI : NF a := ha
  have hnf (k : Nat) : NF (ONote.mulNat a k) := by
    rw [ONote.mulNat_eq_mul]
    infer_instance
  induction n with
  | zero => cases a <;> simp [ONote.mulNat, treeWeight]
  | succ n ih =>
      have hstep : ONote.mulNat a (n + 1) = ONote.mulNat a n + a := by
        haveI : NF (ONote.mulNat a n) := hnf n
        haveI : NF (ONote.mulNat a (n + 1)) := hnf (n + 1)
        apply ONote.repr_inj.mp
        simp only [ONote.mulNat_eq_mul, ONote.repr_mul, ONote.repr_ofNat,
          ONote.repr_add, Nat.cast_add_one, mul_add_one]
      rw [hstep]
      apply (treeWeight_add_le (hnf n) ha).trans
      have hh := Nat.add_le_add_right ih (treeWeight a)
      simpa only [Nat.succ_mul] using hh

theorem principalSum_treeWeight_bound : ∀ {a : ONote}, NF a →
    treeWeight (principalSum a) ≤ triangular (treeWeight a)
  | .zero, _ => le_rfl
  | .oadd e n a, h => by
      haveI : NF e := h.fst
      haveI : NF (principalSum e) := principalSum_nf h.fst
      haveI : NF (principalSum a) := principalSum_nf h.snd
      let v : ONote := ONote.oadd e 1 0 + principalSum e
      have hv : NF v := ONote.add_nf _ _
      have hm : NF (ONote.mulNat v (n : Nat)) := by
        rw [ONote.mulNat_eq_mul]
        infer_instance
      have hcost : treeWeight v ≤ triangular (treeWeight e + 1) := by
        dsimp only [v]
        have h1 := treeWeight_add_le (NF.oadd_zero e 1) (principalSum_nf h.fst)
        have h2 := principalSum_treeWeight_bound h.fst
        simp only [treeWeight, PNat.one_coe, Nat.one_mul, Nat.add_zero, triangular] at h1 ⊢
        omega
      change treeWeight (ONote.mulNat v (n : Nat) + principalSum a) ≤ _
      calc
        _ ≤ treeWeight (ONote.mulNat v (n : Nat)) + treeWeight (principalSum a) :=
          treeWeight_add_le hm (principalSum_nf h.snd)
        _ ≤ (n : Nat) * triangular (treeWeight e + 1) + triangular (treeWeight a) :=
          Nat.add_le_add ((treeWeight_mulNat_le v hv _).trans (Nat.mul_le_mul_left _ hcost))
            (principalSum_treeWeight_bound h.snd)
        _ ≤ triangular ((n : Nat) * (treeWeight e + 1)) + triangular (treeWeight a) :=
          Nat.add_le_add_right (triangular_mul (n : Nat) (treeWeight e + 1)) _
        _ ≤ triangular ((n : Nat) * (treeWeight e + 1) + treeWeight a) := triangular_superadd _ _
        _ = triangular (treeWeight (.oadd e n a)) := by simp only [treeWeight, Nat.add_comm 1]

private theorem lastExponent_treeWeight_lt : ∀ {a : ONote}, a ≠ 0 →
    treeWeight (lastExponent a) + 1 ≤ treeWeight a
  | .zero, ha => (ha rfl).elim
  | .oadd e n a, _ => by
      have hn := n.pos
      have hm : 1 + treeWeight e ≤ (n : Nat) * (1 + treeWeight e) := by
        simpa only [Nat.one_mul] using Nat.mul_le_mul_right (1 + treeWeight e) (Nat.succ_le_of_lt hn)
      cases a with
      | zero => simpa [lastExponent, treeWeight, Nat.add_comm] using hm
      | oadd d m t =>
          have ih := lastExponent_treeWeight_lt (a := .oadd d m t) (by intro h; cases h)
          exact ih.trans (Nat.le_add_left _ _)

private theorem add_triangular_le {n m : Nat} (h : m + 1 ≤ n) :
    n + triangular m ≤ triangular n := by
  cases n with
  | zero => omega
  | succ n =>
      have hm : m ≤ n := by omega
      have ht := triangular_mono hm
      simp only [triangular]
      omega

theorem endpoint_treeWeight_bound {a : ONote} (ha : NF a) :
    treeWeight (endpoint a) ≤ triangular (treeWeight a) := by
  by_cases ha0 : a = 0
  · subst a
    exact le_rfl
  have hnf := principalSum_nf (lastExponent_nf ha)
  exact (treeWeight_add_le ha hnf).trans
    ((Nat.add_le_add_left (principalSum_treeWeight_bound (lastExponent_nf ha)) _).trans
      (add_triangular_le (lastExponent_treeWeight_lt ha0)))

/-- The principal-sum tail fits strictly below its head, so no normalization
can erase any expanded-tree nodes in this principal case. -/
theorem principalSum_principal_normal (e : ONote) (he : NF e) :
    principalSum (ONote.oadd e 1 0) = ONote.oadd e 1 (principalSum e) := by
  haveI : NF e := he
  haveI : NF (principalSum e) := principalSum_nf he
  haveI : NF (ONote.oadd e 1 (principalSum e)) := he.oadd 1
    (NF.below_of_lt' (principalSum_repr_lt_omega_opow he) (principalSum_nf he))
  haveI : NF (principalSum (ONote.oadd e 1 0)) :=
    principalSum_nf (NF.oadd_zero e 1)
  apply ONote.repr_inj.mp
  rw [principalSum_step_repr (1 : ℕ+) (NF.oadd_zero e 1)]
  simp only [ONote.repr, PNat.one_coe, Nat.cast_one, mul_one,
    principalSum_zero, ONote.repr_zero, add_zero]

/-- The endpoint and principal sum agree on a single principal summand. -/
theorem endpoint_principal_eq_principalSum (e : ONote) (he : NF e) :
    endpoint (ONote.oadd e 1 0) = principalSum (ONote.oadd e 1 0) := by
  haveI : NF e := he
  haveI : NF (endpoint (ONote.oadd e 1 0)) := endpoint_nf (NF.oadd_zero e 1)
  haveI : NF (principalSum (ONote.oadd e 1 0)) :=
    principalSum_nf (NF.oadd_zero e 1)
  apply ONote.repr_inj.mp
  rw [endpoint_principal_repr e he,
    principalSum_step_repr (1 : ℕ+) (NF.oadd_zero e 1)]
  simp only [ONote.repr, PNat.one_coe, Nat.cast_one, mul_one,
    principalSum_zero, ONote.repr_zero, add_zero]

/-- Tower height zero is zero; each successor adds one omega-exponent node. -/
def omegaTower : Nat → ONote
  | 0 => 0
  | n + 1 => ONote.oadd (omegaTower n) 1 0

theorem omegaTower_nf : ∀ n, NF (omegaTower n)
  | 0 => NF.zero
  | n + 1 => by
      haveI : NF (omegaTower n) := omegaTower_nf n
      change NF (ONote.oadd (omegaTower n) 1 0)
      infer_instance

@[simp] theorem omegaTower_treeWeight (n : Nat) : treeWeight (omegaTower n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [omegaTower, treeWeight, PNat.one_coe,
      Nat.one_mul, Nat.add_zero, ih, Nat.add_comm 1]

/-- The principal-sum bound is attained at EVERY natural input size. -/
theorem principalSum_omegaTower_treeWeight (n : Nat) :
    treeWeight (principalSum (omegaTower n)) = triangular n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change treeWeight (principalSum (ONote.oadd (omegaTower n) 1 0)) = triangular (n + 1)
      rw [principalSum_principal_normal _ (omegaTower_nf n)]
      simp only [treeWeight, PNat.one_coe, Nat.one_mul, omegaTower_treeWeight, ih, triangular]
      omega

/-- The endpoint bound is sharp for EVERY natural expanded-tree size. -/
theorem endpoint_omegaTower_treeWeight (n : Nat) :
    treeWeight (endpoint (omegaTower n)) = triangular n := by
  cases n with
  | zero => rfl
  | succ n =>
      change treeWeight (endpoint (ONote.oadd (omegaTower n) 1 0)) = triangular (n + 1)
      rw [endpoint_principal_eq_principalSum _ (omegaTower_nf n)]
      exact principalSum_omegaTower_treeWeight (n + 1)

/-- Uniform sharpness, with a normal witness of EACH specified size. -/
theorem endpoint_treeWeight_bound_sharp (n : Nat) :
    ∃ a : ONote, NF a ∧ treeWeight a = n ∧ treeWeight (endpoint a) = triangular n :=
  ⟨omegaTower n, omegaTower_nf n, omegaTower_treeWeight n, endpoint_omegaTower_treeWeight n⟩

#print axioms principalSum_principal_normal
#print axioms principalSum_omegaTower_treeWeight
#print axioms endpoint_omegaTower_treeWeight
#print axioms endpoint_treeWeight_bound_sharp

#print axioms principalSum_treeWeight_bound
#print axioms endpoint_treeWeight_bound

end LogicLineages.OrdinalComparison.Vendor.R1
