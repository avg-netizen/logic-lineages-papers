module
public import LogicLineages.OrdinalComparison.NaturalProduct
public import LogicLineages.OrdinalComparison.NaturalSumInterpretation

@[expose] public section

namespace LogicLineages.OrdinalComparison

universe u

theorem coefficient_foldr_add_acc {ι : Type u} (xs : List ι)
    (f : ι → Ordinal.{0} →₀ Ordinal.{0}) (acc : Ordinal.{0} →₀ Ordinal.{0}) :
    xs.foldr (fun x rest => f x + rest) acc =
      xs.foldr (fun x rest => f x + rest) 0 + acc := by
  induction xs with
  | nil => simp only [List.foldr_nil, zero_add]
  | cons x xs ih => simp only [List.foldr_cons, ih, add_assoc]

theorem normal_cnf_oadd (e : ONote) (c : ℕ+) (t : ONote)
    (h : ONote.NF (.oadd e c t)) :
    Ordinal.CNF Ordinal.omega0 (ONote.oadd e c t).repr =
      (e.repr, ((c : Nat) : Ordinal)) :: Ordinal.CNF Ordinal.omega0 t.repr := by
  have hc : ((c : Nat) : Ordinal) ≠ 0 := by exact_mod_cast c.ne_zero
  exact Ordinal.CNF.opow_mul_add Ordinal.one_lt_omega0 hc
    (Ordinal.natCast_lt_omega0 _) h.snd'.repr_lt

theorem principal_actual_coefficient (e : ONote) (c : ℕ+) :
    Ordinal.CNF.coeff Ordinal.omega0 (ONote.oadd e c .zero).repr =
      Finsupp.single e.repr ((c : Nat) : Ordinal) := by
  have hc : ((c : Nat) : Ordinal) ≠ 0 := by exact_mod_cast c.ne_zero
  have hp : (0 : Ordinal) < Ordinal.omega0 ^ e.repr :=
    Ordinal.opow_pos _ Ordinal.omega0_pos
  simpa only [ONote.repr, ONote.repr_zero, Ordinal.CNF.coeff_zero_right, add_zero] using
    (Ordinal.CNF.coeff_opow_mul_add Ordinal.one_lt_omega0 hc
      (Ordinal.natCast_lt_omega0 _) hp)

theorem rawNaturalSum_coefficient_finsupp (a b : ONote) (ha : ONote.NF a)
    (hb : ONote.NF b) :
    Ordinal.CNF.coeff Ordinal.omega0 (rawNaturalSum a b).repr =
      Ordinal.CNF.coeff Ordinal.omega0 a.repr +
        Ordinal.CNF.coeff Ordinal.omega0 b.repr := by
  apply Finsupp.ext
  intro q
  exact naturalSumOrdinalCoefficients ⟨a, ha⟩ ⟨b, hb⟩ q

theorem rawMonomialProduct_actual_coefficients (e : ONote) (he : ONote.NF e) (c : ℕ+) :
    ∀ b : ONote, ONote.NF b →
      Ordinal.CNF.coeff Ordinal.omega0 (rawMonomialProduct e c b).repr =
        (Ordinal.CNF Ordinal.omega0 b.repr).foldr
          (fun q rest => Finsupp.single (ordinalNaturalSum e.repr q.1)
            (((c : Nat) : Ordinal) * q.2) + rest) 0
  | .zero, _ => by
      simp only [rawMonomialProduct, ONote.repr_zero, Ordinal.CNF.coeff_zero_right,
        Ordinal.CNF.zero_right, List.foldr_nil]
  | .oadd f d u, hb => by
      have hprincipal : ONote.NF (.oadd (rawNaturalSum e f) (c * d) .zero) :=
        ONote.NF.oadd (rawNaturalSum_normal e f he hb.fst) (c * d) ONote.NFBelow.zero
      have hrec := rawMonomialProduct_normal e he c u hb.snd
      rw [rawMonomialProduct,
        rawNaturalSum_coefficient_finsupp _ _ hprincipal hrec,
        principal_actual_coefficient,
        rawMonomialProduct_actual_coefficients e he c u hb.snd]
      have hexp : (rawNaturalSum e f).repr = ordinalNaturalSum e.repr f.repr :=
        naturalSumDenotation ⟨e, he⟩ ⟨f, hb.fst⟩
      have hcoef : (((c * d : ℕ+) : Nat) : Ordinal) =
          ((c : Nat) : Ordinal) * ((d : Nat) : Ordinal) := by
        simp only [PNat.mul_coe, Ordinal.natCast_mul]
      rw [hexp, hcoef, normal_cnf_oadd f d u hb, List.foldr_cons]

theorem rawNaturalProduct_actual_coefficients : ∀ a : ONote, ONote.NF a →
    ∀ b : ONote, ONote.NF b →
      Ordinal.CNF.coeff Ordinal.omega0 (rawNaturalProduct a b).repr =
        (Ordinal.CNF Ordinal.omega0 a.repr).foldr
          (fun p acc => (Ordinal.CNF Ordinal.omega0 b.repr).foldr
            (fun q rest => Finsupp.single (ordinalNaturalSum p.1 q.1) (p.2 * q.2) + rest)
            acc) 0
  | .zero, _, _, _ => by
      simp only [rawNaturalProduct, ONote.repr_zero, Ordinal.CNF.coeff_zero_right,
        Ordinal.CNF.zero_right, List.foldr_nil]
  | .oadd e c t, ha, b, hb => by
      have hm := rawMonomialProduct_normal e ha.fst c b hb
      have ht := rawNaturalProduct_normal t ha.snd b hb
      rw [rawNaturalProduct, rawNaturalSum_coefficient_finsupp _ _ hm ht,
        rawMonomialProduct_actual_coefficients e ha.fst c b hb,
        rawNaturalProduct_actual_coefficients t ha.snd b hb,
        normal_cnf_oadd e c t ha, List.foldr_cons]
      exact (coefficient_foldr_add_acc (Ordinal.CNF Ordinal.omega0 b.repr)
        (fun q => Finsupp.single (ordinalNaturalSum e.repr q.1)
          (((c : Nat) : Ordinal) * q.2)) _).symm

theorem naturalProductDenotation : Targets.NaturalProductDenotation naturalProduct := by
  intro a b
  calc
    (naturalProduct a b).1.repr = Ordinal.CNF.eval Ordinal.omega0
        (Ordinal.CNF.coeff Ordinal.omega0 (naturalProduct a b).1.repr) :=
      (Ordinal.CNF.eval_coeff _ _).symm
    _ = ordinalNaturalProduct a.1.repr b.1.repr := by
      change Ordinal.CNF.eval Ordinal.omega0
        (Ordinal.CNF.coeff Ordinal.omega0 (rawNaturalProduct a.1 b.1).repr) = _
      rw [rawNaturalProduct_actual_coefficients a.1 a.2 b.1 b.2]
      rfl

end LogicLineages.OrdinalComparison
