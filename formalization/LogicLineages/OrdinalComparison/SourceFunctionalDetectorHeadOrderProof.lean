module
public import LogicLineages.OrdinalComparison.SourceFunctionalDetectorSumOrderProof
public import LogicLineages.OrdinalComparison.SourceFunctionalDetectorOmegaOrderProof
public import LogicLineages.OrdinalComparison.SourceFunctionalDetectorValuesProof
public import Mathlib.Tactic.NormNum
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalDetector.Proof

private theorem monomial_zero_coeff (c : ℕ+) : ∀ (t : ONote), ONote.NF t → ∀ e : Ordinal,
    Ordinal.CNF.coeff Ordinal.omega0 (rawMonomialProduct .zero c t).repr e=
      ((c : Nat) : Ordinal)*Ordinal.CNF.coeff Ordinal.omega0 t.repr e
  | .zero, _, e => by simp [rawMonomialProduct,ONote.repr]
  | .oadd f d u, ht, e => by
    rw [rawMonomialProduct,rawNaturalSum_coefficient_finsupp]
    · rw [principal_actual_coefficient]
      simp only [Finsupp.add_apply,monomial_zero_coeff c u ht.snd e,rawNaturalSum]
      rw [show Ordinal.CNF.coeff Ordinal.omega0 (ONote.oadd f d u).repr=
        Finsupp.single f.repr ((d : Nat) : Ordinal)+Ordinal.CNF.coeff Ordinal.omega0 u.repr by
          exact Ordinal.CNF.coeff_opow_mul_add Ordinal.one_lt_omega0
            (by exact_mod_cast d.ne_zero) (Ordinal.natCast_lt_omega0 _) ht.snd'.repr_lt]
      simp only [Finsupp.add_apply,mul_add]
      by_cases he : f.repr=e
      · simp [Finsupp.single_apply,he,PNat.mul_coe,Ordinal.natCast_mul]
      · simp [Finsupp.single_apply,he]
    · exact ONote.NF.oadd (rawNaturalSum_normal .zero f ONote.NF.zero ht.fst) _ ONote.NFBelow.zero
    · exact rawMonomialProduct_normal .zero ONote.NF.zero c u ht.snd

theorem finite_product_coeff (c : ℕ+) (h : Ordinal) (hh : h<epsilonZero) (e : Ordinal) :
    Ordinal.CNF.coeff Ordinal.omega0 (ordinalNaturalProduct ((c : Nat) : Ordinal) h) e=
      ((c : Nat) : Ordinal)*Ordinal.CNF.coeff Ordinal.omega0 h e := by
  obtain ⟨t,ht⟩ := normalRepresentationComplete h hh
  let n : NONote := ⟨.oadd .zero c .zero,ONote.NF.oadd ONote.NF.zero c ONote.NFBelow.zero⟩
  have hn : n.1.repr=((c : Nat) : Ordinal) := by simp [n,ONote.repr]
  rw [← hn,← ht,← naturalProductDenotation]
  have he : rawNaturalProduct n.1 t.1=rawMonomialProduct .zero c t.1 := by
    change rawNaturalSum (rawMonomialProduct .zero c t.1) .zero=_
    cases rawMonomialProduct .zero c t.1 <;> simp only [rawNaturalSum]
  change Ordinal.CNF.coeff Ordinal.omega0 (rawNaturalProduct n.1 t.1).repr e=_
  rw [he,hn]
  exact monomial_zero_coeff c t.1 t.2 e

theorem four_product (h : Ordinal) (hh : h<epsilonZero) :
    ordinalNaturalProduct 4 h=ordinalNaturalSum (ordinalNaturalSum h h) (ordinalNaturalSum h h) := by
  apply Ordinal.CNF.coeff_injective Ordinal.omega0
  ext e
  have hc := finite_product_coeff (4 : ℕ+) h hh e
  norm_num at hc
  rw [hc]
  simp only [sum_coeff,Finsupp.add_apply]
  obtain ⟨n,hn⟩ := Ordinal.lt_omega0.mp (coeff_finite h e)
  rw [hn]
  exact_mod_cast (show 4*n=(n+n)+(n+n) by omega)

theorem double_strict (a b : Ordinal) (hab : a<b) :
    ordinalNaturalSum a a<ordinalNaturalSum b b :=
  (sum_strict_right a b a hab).trans (sum_strict_left a b b hab)

theorem four_product_strict (a b : Ordinal) (ha : a<epsilonZero) (hb : b<epsilonZero) (hab : a<b) :
    ordinalNaturalProduct 4 a<ordinalNaturalProduct 4 b := by
  rw [four_product a ha,four_product b hb]
  exact double_strict _ _ (double_strict a b hab)

theorem paddedHead_strict (a b : Ordinal) (hab : a<b) : paddedHead a<paddedHead b := by
  unfold paddedHead
  have h := sum_strict_left _ _ 1 (sum_strict_right a b 1 hab)
  exact (sum_strict_right _ _ a h).trans (sum_strict_left a b _ hab)

theorem sum_below_epsilon (a b : Ordinal) (ha : a<epsilonZero) (hb : b<epsilonZero) :
    ordinalNaturalSum a b<epsilonZero := by
  obtain ⟨x,hx⟩ := normalRepresentationComplete a ha
  obtain ⟨y,hy⟩ := normalRepresentationComplete b hb
  rw [← hx,← hy,← naturalSumDenotation]
  exact normalRepresentationSound _

theorem paddedHead_below (a : Ordinal) (ha : a<epsilonZero) : paddedHead a<epsilonZero := by
  have h1 : (1 : Ordinal)<epsilonZero := by
    simpa only [ONote.repr_one,Nat.cast_one] using normalRepresentationSound (⟨1,ONote.nf_one⟩ : NONote)
  exact sum_below_epsilon _ _ (sum_below_epsilon _ _ h1 (sum_below_epsilon _ _ ha h1)) ha
theorem headCombine_four (a b : Ordinal) :
    headCombine a b=ordinalNaturalProduct 4 (ordinalNaturalSum (paddedHead a) (paddedHead b)) := by
  unfold headCombine
  have hf : (2 : Ordinal)^(ordinalNaturalSum 1 1)=4 := by
    have hs := actualNaturalSumFiniteRight (1 : Ordinal) 1
    norm_num at hs
    rw [hs]
    have hp := Ordinal.opow_natCast (2 : Ordinal) 2
    norm_num [pow_two] at hp
    exact hp.trans (by exact_mod_cast (show (2 : Nat)*2=4 by decide))
  rw [hf]

theorem headCombine_strict_left (a b c : Ordinal)
    (ha : a<epsilonZero) (hb : b<epsilonZero) (hc : c<epsilonZero) (hab : a<b) :
    headCombine a c<headCombine b c := by
  rw [headCombine_four,headCombine_four]
  exact four_product_strict _ _
    (sum_below_epsilon _ _ (paddedHead_below a ha) (paddedHead_below c hc))
    (sum_below_epsilon _ _ (paddedHead_below b hb) (paddedHead_below c hc))
    (sum_strict_right _ _ _ (paddedHead_strict a b hab))

theorem headCombine_strict_right (a b c : Ordinal)
    (ha : a<epsilonZero) (hb : b<epsilonZero) (hc : c<epsilonZero) (hab : a<b) :
    headCombine c a<headCombine c b := by
  rw [headCombine_four,headCombine_four,sum_comm (paddedHead c) (paddedHead a),
    sum_comm (paddedHead c) (paddedHead b)]
  rw [← headCombine_four,← headCombine_four]
  exact headCombine_strict_left a b c ha hb hc hab
end LogicLineages.OrdinalComparison.Source.FunctionalDetector.Proof
