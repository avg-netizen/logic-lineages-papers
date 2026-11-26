module
public import LogicLineages.CartierObserverCurrent.RootInterpolationTargets
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.CartierObserverCurrent.RootInterpolation
open SplittingRoots Polynomial

theorem productDegree : Targets.ProductDegree := by
  intro d
  constructor
  · exact monic_prod_of_monic _ _ (fun z _ => monic_X_sub_C z)
  · exact natDegree_finsetProd_X_sub_C_eq_card _ id

theorem omittedFactor : Targets.OmittedFactor := by
  intro d z
  classical
  exact (Finset.mul_prod_erase (rootSet d) (fun a => X - C a) z.property).symm

theorem omittedNonzero : Targets.OmittedNonzero := by
  intro d z
  classical
  simp only [omittedProduct, eval_prod, eval_sub, eval_X, eval_C]
  apply Finset.prod_ne_zero_iff.mpr
  intro a ha
  exact sub_ne_zero.mpr (Finset.mem_erase.mp ha).1.symm

theorem omittedDegree : Targets.OmittedDegree := by
  intro d z
  classical
  have hm : (omittedProduct d z.val).Monic :=
    monic_prod_of_monic _ _ (fun a _ => monic_X_sub_C a)
  rw [degree_eq_natDegree hm.ne_zero]
  have hn : (omittedProduct d z.val).natDegree = ((rootSet d).erase z.val).card :=
    natDegree_finsetProd_X_sub_C_eq_card _ id
  rw [hn]
  exact WithBot.coe_lt_coe.mpr (Finset.card_erase_lt_of_mem z.property)

private theorem omitted_other (d : Nat) (z a : FieldAt d)
    (hz : z ∈ rootSet d) (hne : a ≠ z) : (omittedProduct d a).eval z = 0 := by
  classical
  simp only [omittedProduct, eval_prod, eval_sub, eval_X, eval_C]
  apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hne.symm, hz⟩)
  exact sub_self z

theorem interpolationNodes : Targets.InterpolationNodes := by
  intro d U z
  classical
  simp only [interpolate, eval_finset_sum, eval_mul, eval_C]
  rw [Finset.sum_eq_single z.val]
  · exact div_mul_cancel₀ _ (omittedNonzero d z)
  · intro a _ ha
    rw [omitted_other d z.val a z.property ha, mul_zero]
  · exact fun h => False.elim (h z.property)

private theorem interpolation_degree (d : Nat) (U : Polynomial (FieldAt d)) :
    (interpolate d U).degree < ((rootSet d).card : WithBot Nat) := by
  classical
  apply (degree_sum_le _ _).trans_lt
  apply (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr
  intro z hz
  have h := degree_smul_le (U.eval z / (omittedProduct d z).eval z) (omittedProduct d z)
  rw [smul_eq_C_mul] at h
  exact h.trans_lt (omittedDegree d ⟨z, hz⟩)

theorem interpolationComplete : Targets.InterpolationComplete := by
  intro d U hU
  classical
  have hI := interpolation_degree d U
  by_cases hempty : (rootSet d).card = 0
  · have hu : U = 0 := degree_lt_zero.mp (by simpa [hempty] using hU)
    have hi : interpolate d U = 0 := degree_lt_zero.mp (by simpa [hempty] using hI)
    exact hi.trans hu.symm
  · have hp : 0 < (rootSet d).card := Nat.pos_of_ne_zero hempty
    have hn (P : Polynomial (FieldAt d))
        (hP : P.degree < ((rootSet d).card : WithBot Nat)) : P.natDegree < (rootSet d).card := by
      by_cases hzero : P = 0
      · simpa [hzero] using hp
      · rw [degree_eq_natDegree hzero] at hP
        exact WithBot.coe_lt_coe.mp hP
    apply eq_of_natDegree_lt_card_of_eval_eq' (interpolate d U) U (rootSet d)
    · intro z hz
      exact interpolationNodes d U ⟨z, hz⟩
    · exact max_lt (hn _ hI) (hn _ hU)

#audit_namespace LogicLineages.CartierObserverCurrent.RootInterpolation
end LogicLineages.CartierObserverCurrent.RootInterpolation
