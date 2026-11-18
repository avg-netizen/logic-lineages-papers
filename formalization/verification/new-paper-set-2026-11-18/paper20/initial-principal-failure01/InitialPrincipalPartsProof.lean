module
public import LogicLineages.CartierObserverCurrent.InitialPrincipalPartsTargets
public import LogicLineages.CartierObserverCurrent.SplitSupportProof
public import LogicLineages.CartierObserverCurrent.SourceBudgetProof
public import LogicLineages.CartierObserverCurrent.MixedProperProof
public import Mathlib.Algebra.BigOperators.Field
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.CartierObserverCurrent.InitialPrincipalParts
open SplittingRoots RootInterpolation Polynomial

private noncomputable instance rootFintype (d : Nat) : Fintype (Root d) := by
  classical
  unfold Root
  infer_instance

private theorem power_ne_zero (d M : Nat) : (rootProduct d) ^ M ≠ 0 :=
  pow_ne_zero _ (productDegree d).1.ne_zero

private theorem source_ne_zero (d : Nat) : splitPolynomial d ≠ 0 := by
  rw [splitPolynomial, SourceBudget.sourceMap]
  intro h
  have hc := SourceBudget.sourceConstant (FieldAt d) d
  rw [h, coeff_zero] at hc
  exact zero_ne_one hc

theorem sourceDivisibility : Targets.SourceDivisibility := by
  intro d
  classical
  rw [(actualSplitting d).dvd_iff_roots_le_roots (source_ne_zero d)
    (power_ne_zero d (SourceBudget.budget d)), roots_pow, SplitSupport.productRoots]
  apply Multiset.le_iff_count.mpr
  intro z
  by_cases hz : z ∈ (splitPolynomial d).roots
  · have hs : z ∈ (SplittingRoots.rootSet d).val := by
      exact (exactAllRoots d z).mpr ((mem_roots (source_ne_zero d)).mp hz)
    rw [Multiset.count_nsmul, Multiset.count_eq_one_of_mem
      (SplittingRoots.rootSet d).nodup hs, mul_one, count_roots]
    rw [splitPolynomial, SourceBudget.sourceMap]
    exact SourceBudget.sourceMultiplicity (FieldAt d) d z
  · rw [Multiset.count_eq_zero_of_notMem hz]
    exact Nat.zero_le _

theorem boundedPresentation : Targets.BoundedPresentation := by
  intro d M f
  constructor
  · rintro ⟨hproper, q, hq⟩
    have hq0 : q ≠ 0 := by
      intro h; rw [h, mul_zero] at hq
      exact power_ne_zero d M hq
    refine ⟨f.num * q, ?_, ?_⟩
    · by_cases hf : f = 0
      · simp only [hf, RatFunc.num_zero, zero_mul, degree_zero]
        exact WithBot.bot_lt_iff_ne_bot.mpr (mt degree_eq_bot.mp (power_ne_zero d M))
      · change f.num.degree < f.denom.degree at hproper
        rw [degree_eq_natDegree (RatFunc.num_ne_zero hf), degree_eq_natDegree f.denom_ne_zero] at hproper
        rw [hq, degree_eq_natDegree (mul_ne_zero (RatFunc.num_ne_zero hf) hq0),
          degree_eq_natDegree (mul_ne_zero f.denom_ne_zero hq0),
          natDegree_mul (RatFunc.num_ne_zero hf) hq0, natDegree_mul f.denom_ne_zero hq0]
        exact WithBot.coe_lt_coe.mpr (Nat.add_lt_add_right (WithBot.coe_lt_coe.mp hproper) _)
    · rw [hq, map_mul, map_mul, mul_div_mul_right _ _ (RatFunc.algebraMap_ne_zero hq0)]
      exact f.num_div_denom.symm
  · rintro ⟨U, hU, rfl⟩
    exact ⟨MixedProper.fractionProper _ _ _ hU, RatFunc.denom_div_dvd _ _⟩

private theorem factor_coprime (d : Nat) :
    Set.Pairwise (Finset.univ : Finset (Root d))
      (fun z a => IsCoprime (X - C z.val) (X - C a.val)) := by
  intro z _ a _ h
  apply isCoprime_X_sub_C_of_isUnit_sub
  exact (sub_ne_zero.mpr (fun he => h (Subtype.ext he))).isUnit

private theorem factor_inverse (d : Nat) (z : Root d) :
    (Basic.rationalX - Basic.rationalC z.val : RatFunc (FieldAt d))⁻¹ *
      algebraMap (Polynomial (FieldAt d)) (RatFunc (FieldAt d)) (X - C z.val) = 1 := by
  have hn : (X - C z.val : Polynomial (FieldAt d)) ≠ 0 := (monic_X_sub_C z.val).ne_zero
  have he : algebraMap (Polynomial (FieldAt d)) (RatFunc (FieldAt d)) (X - C z.val) =
      Basic.rationalX - Basic.rationalC z.val := by
    rw [map_sub]
    congr 1
    exact (IsScalarTower.algebraMap_apply (FieldAt d) (Polynomial (FieldAt d))
      (RatFunc (FieldAt d)) z.val).symm
  rw [← he]
  exact inv_mul_cancel₀ (RatFunc.algebraMap_ne_zero hn)

private theorem embed_C (d : Nat) (x : FieldAt d) :
    algebraMap (Polynomial (FieldAt d)) (RatFunc (FieldAt d)) (C x) = Basic.rationalC x :=
  (IsScalarTower.algebraMap_apply (FieldAt d) (Polynomial (FieldAt d)) (RatFunc (FieldAt d)) x).symm

theorem fullUniqueness : Targets.FullUniqueness := by
  intro d M q r b c he
  classical
  have h := quo_add_sum_rem_mul_pow_inverse_unique
    (s := Finset.univ) (g := fun z : Root d => X - C z.val)
    (n := fun _ => M)
    (gi := fun z : Root d => (Basic.rationalX - Basic.rationalC z.val : RatFunc (FieldAt d))⁻¹)
    (fun z _ => monic_X_sub_C z.val) (factor_coprime d)
    (fun z _ => factor_inverse d z)
    (q₁ := q) (q₂ := r)
    (r₁ := fun z j => C (b z j)) (r₂ := fun z j => C (c z j))
    (fun z _ j => by simpa using (degree_C_le.trans_lt (show (0 : WithBot Nat) < 1 by decide)))
    (fun z _ j => by simpa using (degree_C_le.trans_lt (show (0 : WithBot Nat) < 1 by decide)))
    (by simpa [reconstruct, embed_C, div_eq_mul_inv, inv_pow] using he)
  refine ⟨h.1, ?_⟩
  funext z j
  exact C_injective (congrFun (h.2 z (Finset.mem_univ z)) j)


private noncomputable def commonNumerator (d M : Nat) (b : Coefficients d M) : Polynomial (FieldAt d) := by
  classical
  exact ∑ z : Root d, ∑ j : Fin M,
    C (b z j) * ((X - C z.val) ^ (M - (j.val + 1)) * (omittedProduct d z.val) ^ M)

private theorem numerator_degree (d M : Nat) (b : Coefficients d M) :
    (commonNumerator d M b).degree < ((rootProduct d) ^ M).degree := by
  classical
  have hT := (productDegree d).1.ne_zero
  have hbot : (⊥ : WithBot Nat) < ((rootProduct d) ^ M).degree :=
    WithBot.bot_lt_iff_ne_bot.mpr (mt degree_eq_bot.mp (power_ne_zero d M))
  unfold commonNumerator
  apply (degree_sum_le _ _).trans_lt
  apply (Finset.sup_lt_iff hbot).mpr
  intro z _
  apply (degree_sum_le _ _).trans_lt
  apply (Finset.sup_lt_iff hbot).mpr
  intro j _
  have hD : omittedProduct d z.val ≠ 0 := by
    intro h; have hn := omittedNonzero d z; rw [h, eval_zero] at hn; exact hn rfl
  have hF : (X - C z.val : Polynomial (FieldAt d)) ≠ 0 := (monic_X_sub_C z.val).ne_zero
  have htdeg : (rootProduct d).natDegree = 1 + (omittedProduct d z.val).natDegree := by
    rw [omittedFactor d z, natDegree_mul hF hD, natDegree_X_sub_C]
  have hsm := degree_smul_le (b z j)
    ((X - C z.val) ^ (M - (j.val + 1)) * (omittedProduct d z.val) ^ M)
  rw [smul_eq_C_mul] at hsm
  apply hsm.trans_lt
  rw [degree_eq_natDegree (mul_ne_zero (pow_ne_zero _ hF) (pow_ne_zero _ hD)),
    degree_eq_natDegree (pow_ne_zero M hT),
    natDegree_mul (pow_ne_zero _ hF) (pow_ne_zero _ hD), natDegree_pow,
    natDegree_pow, natDegree_pow, natDegree_X_sub_C, htdeg]
  apply WithBot.coe_lt_coe.mpr
  have hj := j.isLt
  omega

private theorem common_fraction (d M : Nat) (b : Coefficients d M) :
    reconstruct d M b =
      algebraMap (Polynomial (FieldAt d)) (RatFunc (FieldAt d)) (commonNumerator d M b) /
        algebraMap (Polynomial (FieldAt d)) (RatFunc (FieldAt d)) ((rootProduct d) ^ M) := by
  classical
  unfold reconstruct commonNumerator
  rw [map_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro z _
  rw [map_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  have hF : (Basic.rationalX - Basic.rationalC z.val : RatFunc (FieldAt d)) ≠ 0 := by
    intro h
    have hn := factor_inverse d z
    rw [h, inv_zero, zero_mul] at hn
    exact zero_ne_one hn
  have hD : algebraMap (Polynomial (FieldAt d)) (RatFunc (FieldAt d))
      (omittedProduct d z.val) ≠ 0 := RatFunc.algebraMap_ne_zero (by
        intro h; have hn := omittedNonzero d z; rw [h, eval_zero] at hn; exact hn rfl)
  rw [map_mul, map_mul, map_pow, map_pow, embed_C, map_sub, embed_C,
    omittedFactor d z, map_pow, map_mul, map_sub, embed_C]
  change _ = _ / (((Basic.rationalX - Basic.rationalC z.val) * _) ^ M)
  rw [mul_pow, mul_div_mul_right _ _ (pow_ne_zero M hD)]
  apply (eq_div_iff (pow_ne_zero M hF)).mpr
  have hj : M = M - (j.val + 1) + (j.val + 1) := by omega
  conv_lhs => rw [hj, pow_add]
  field_simp
  <;> ring

private theorem reconstruction_bounded (d M : Nat) (b : Coefficients d M) :
    bounded d M (reconstruct d M b) := by
  apply (boundedPresentation d M _).mpr
  exact ⟨commonNumerator d M b, numerator_degree d M b, common_fraction d M b⟩

private theorem coefficient_constant {d : Nat} {P : Polynomial (FieldAt d)}
    (h : P.degree < 1) : P = C (P.coeff 0) := by
  apply Polynomial.ext
  intro n
  by_cases hn : n = 0
  · subst n; simp
  · rw [coeff_C, if_neg hn]
    apply coeff_eq_zero_of_degree_lt
    exact h.trans_le (WithBot.coe_le_coe.mpr (Nat.one_le_iff_ne_zero.mpr hn))

private theorem polynomial_part_zero (d M : Nat) (U q : Polynomial (FieldAt d))
    (b : Coefficients d M) (hU : U.degree < ((rootProduct d)^M).degree)
    (he : algebraMap (Polynomial (FieldAt d)) (RatFunc (FieldAt d)) U /
        algebraMap (Polynomial (FieldAt d)) (RatFunc (FieldAt d)) ((rootProduct d)^M) =
      algebraMap (Polynomial (FieldAt d)) (RatFunc (FieldAt d)) q + reconstruct d M b) :
    q = 0 := by
  rw [common_fraction] at he
  have hD := RatFunc.algebraMap_ne_zero (power_ne_zero d M)
  have hp : U = q * (rootProduct d)^M + commonNumerator d M b := by
    apply RatFunc.algebraMap_injective
    rw [map_add, map_mul]
    have hc := congrArg (fun x : RatFunc (FieldAt d) =>
      x * algebraMap (Polynomial (FieldAt d)) (RatFunc (FieldAt d)) ((rootProduct d)^M)) he
    simpa only [add_mul, div_mul_cancel₀ _ hD] using hc
  have hrem := numerator_degree d M b
  have hdeg : (q * (rootProduct d)^M).degree < ((rootProduct d)^M).degree := by
    have heq : q * (rootProduct d)^M = U - commonNumerator d M b := by rw [hp]; ring
    rw [heq]
    exact (degree_sub_le _ _).trans_lt (max_lt hU hrem)
  by_contra hq
  rw [degree_eq_natDegree (mul_ne_zero hq (power_ne_zero d M)),
    degree_eq_natDegree (power_ne_zero d M), natDegree_mul hq (power_ne_zero d M)] at hdeg
  have := WithBot.coe_lt_coe.mp hdeg
  omega

private theorem source_product (d M : Nat) :
    (∏ z : Root d, (X - C z.val : Polynomial (FieldAt d)) ^ M) = (rootProduct d)^M := by
  classical
  rw [← Finset.prod_pow]
  congr 1
  exact Finset.prod_coe_sort (SplittingRoots.rootSet d) (fun z => X - C z)

private theorem existence (d M : Nat) (U : Polynomial (FieldAt d)) :
    ∃ q : Polynomial (FieldAt d), ∃ b : Coefficients d M,
      algebraMap (Polynomial (FieldAt d)) (RatFunc (FieldAt d)) U /
          algebraMap (Polynomial (FieldAt d)) (RatFunc (FieldAt d)) ((rootProduct d)^M) =
        algebraMap (Polynomial (FieldAt d)) (RatFunc (FieldAt d)) q + reconstruct d M b := by
  classical
  obtain ⟨q, r, hr, he⟩ := mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse
    (s := Finset.univ) U (g := fun z : Root d => X - C z.val)
    (fun z _ => monic_X_sub_C z.val) (factor_coprime d) (fun _ => M)
    (gi := fun z : Root d => (Basic.rationalX - Basic.rationalC z.val : RatFunc (FieldAt d))⁻¹)
    (fun z _ => factor_inverse d z)
  refine ⟨q, fun z j => (r z j).coeff 0, ?_⟩
  have hconst : ∀ z j, r z j = C ((r z j).coeff 0) := by
    intro z j
    apply coefficient_constant
    simpa using hr z (Finset.mem_univ z) j
  have hprod : (∏ z : Root d,
      (Basic.rationalX - Basic.rationalC z.val : RatFunc (FieldAt d))⁻¹ ^ M) =
      (algebraMap (Polynomial (FieldAt d)) (RatFunc (FieldAt d)) ((rootProduct d)^M))⁻¹ := by
    rw [← source_product, map_prod]
    simp only [map_pow, map_sub, embed_C]
    simp only [inv_pow, ← Finset.prod_inv_distrib]
    rfl
  rw [hprod] at he
  simpa only [hconst, embed_C, reconstruct, div_eq_mul_inv, inv_pow] using he

theorem properCoverage : Targets.ProperCoverage := by
  intro d M f
  constructor
  · intro hf
    obtain ⟨U, hU, rfl⟩ := (boundedPresentation d M f).mp hf
    obtain ⟨q, b, hb⟩ := existence d M U
    have hq := polynomial_part_zero d M U q b hU hb
    rw [hq, map_zero, zero_add] at hb
    refine ⟨b, hb.symm, ?_⟩
    intro c hc
    exact (fullUniqueness d M 0 0 c b (by simpa using hc.trans hb)).2
  · rintro ⟨b, hb, _⟩
    rw [← hb]
    exact reconstruction_bounded d M b

theorem initialSourceCoverage : Targets.InitialSourceCoverage := by
  intro d hd P hP
  apply (properCoverage d (SourceBudget.budget d) (source d P)).mp
  have hp := SourceBudget.mappedProperInput (ZMod 2) (FieldAt d)
    (algebraMap (ZMod 2) (FieldAt d)) d P hP
  refine ⟨?_, ?_⟩
  · simpa [source, splitPolynomial, SourceBudget.sourceMap] using hp.2.2
  · exact (RatFunc.denom_div_dvd _ _).trans (sourceDivisibility d)

#audit_namespace LogicLineages.CartierObserverCurrent.InitialPrincipalParts
end LogicLineages.CartierObserverCurrent.InitialPrincipalParts
