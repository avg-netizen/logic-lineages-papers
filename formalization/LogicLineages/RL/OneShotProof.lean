module

public import LogicLineages.RL.OneShotTargets
public import LogicLineages.RL.PolicySemanticsProof
public import Mathlib.Data.Rat.BigOperators

@[expose] public section

namespace LogicLineages.RL.Policy.OneShotProof

open Filter Topology

variable {S : Alphabet}

/-- Rational expectation of the actual continuation trace from a recorded
history; this is a finite sum, not an extra value specification. -/
def expectationFrom (p : SPolicy S) (μ : SEnvironment S) (n : ℕ)
    (h : EnvHistory S) : ℚ :=
  ∑ tr : PositiveTrace S n, positiveWeight p μ n h tr * (positiveReward n tr : ℚ)

theorem expectationFrom_succ (p : SPolicy S) (μ : SEnvironment S)
    (n : ℕ) (h : EnvHistory S) :
    expectationFrom p μ (n + 1) h =
      ∑ z : S.Percept, ∑ a : S.Action,
        (μ h).mass z * (p (h, z)).mass a *
          ((S.reward z : ℚ) + expectationFrom p μ n (h ++ [(z, a)])) := by
  unfold expectationFrom
  change (∑ tr : S.Percept × S.Action × PositiveTrace S n,
    ((μ h).mass tr.1 * (p (h, tr.1)).mass tr.2.1 *
      positiveWeight p μ n (h ++ [(tr.1, tr.2.1)]) tr.2.2) *
      ((S.reward tr.1 + positiveReward n tr.2.2 : ℤ) : ℚ)) = _
  simp only [Fintype.sum_prod_type, Int.cast_add]
  apply Finset.sum_congr rfl
  intro z hz
  apply Finset.sum_congr rfl
  intro a ha
  have hn := PolicySemanticsProof.positiveWeight_sum p μ n (h ++ [(z, a)])
  calc
    (∑ tr : PositiveTrace S n,
      ((μ h).mass z * (p (h, z)).mass a * positiveWeight p μ n (h ++ [(z, a)]) tr) *
        ((S.reward z : ℚ) + (positiveReward n tr : ℚ))) =
        (μ h).mass z * (p (h, z)).mass a *
          ((S.reward z : ℚ) * (∑ tr : PositiveTrace S n,
            positiveWeight p μ n (h ++ [(z, a)]) tr) +
            ∑ tr : PositiveTrace S n,
              positiveWeight p μ n (h ++ [(z, a)]) tr * (positiveReward n tr : ℚ)) := by
      simp only [Finset.mul_sum, Finset.sum_add_distrib, mul_add]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro tr htr <;> ring
    _ = _ := by rw [hn]; simp

theorem expectationFrom_det_zero (p : SPolicy S) (μ : DEnvironment S)
    (h : EnvHistory S) :
    expectationFrom p (embedEnvironment μ) 0 h = (S.reward (μ h) : ℚ) := by
  classical
  simp [expectationFrom, PositiveTrace, positiveWeight, positiveReward, embedEnvironment, dirac]

theorem expectationFrom_det_succ (p : SPolicy S) (μ : DEnvironment S)
    (n : ℕ) (h : EnvHistory S) :
    expectationFrom p (embedEnvironment μ) (n + 1) h =
      (S.reward (μ h) : ℚ) +
        ∑ a : S.Action, (p (h, μ h)).mass a *
          expectationFrom p (embedEnvironment μ) n (h ++ [(μ h, a)]) := by
  classical
  rw [expectationFrom_succ]
  simp only [mul_assoc, ← Finset.mul_sum]
  simp only [embedEnvironment, dirac]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, Kernel.sum_one, one_mul]

theorem oneShotOffPathRule (S : Alphabet) : Targets.OneShotOffPathRule S := by
  intro test
  refine ⟨rfl, fun _ _ => rfl, ?_⟩
  intro h hh
  cases h with
  | nil => simp at hh
  | cons x h =>
      cases h with
      | nil => simp at hh
      | cons y h => rfl

theorem oneShot_late (test : S.Action → Bool) (h : EnvHistory S) (hh : 2 ≤ h.length) :
    oneShot test h = S.zeroPercept := (oneShotOffPathRule S test).2.2 h hh

theorem expectationFrom_late (test : S.Action → Bool) (p : SPolicy S) (n : ℕ) :
    ∀ h : EnvHistory S, 2 ≤ h.length →
      expectationFrom p (embedEnvironment (oneShot test)) n h = 0 := by
  induction n with
  | zero =>
      intro h hh
      rw [expectationFrom_det_zero, oneShot_late test h hh, S.reward_zero]
      simp
  | succ n ih =>
      intro h hh
      rw [expectationFrom_det_succ, oneShot_late test h hh, S.reward_zero]
      simp only [Int.cast_zero, zero_add]
      apply Finset.sum_eq_zero
      intro a ha
      rw [ih (h ++ [(S.zeroPercept, a)]) (by simp; omega), mul_zero]

theorem expectationFrom_second (test : S.Action → Bool) (p : SPolicy S)
    (n : ℕ) (z : S.Percept) (a : S.Action) :
    expectationFrom p (embedEnvironment (oneShot test)) n [(z, a)] =
      if test a then 1 else 0 := by
  cases n with
  | zero =>
      rw [expectationFrom_det_zero]
      simp only [oneShot]
      split <;> simp_all [S.reward_one, S.reward_zero]
  | succ n =>
      rw [expectationFrom_det_succ]
      have hs : (∑ b : S.Action, (p ([(z, a)], oneShot test [(z, a)])).mass b *
          expectationFrom p (embedEnvironment (oneShot test)) n
            ([(z, a)] ++ [(oneShot test [(z, a)], b)])) = 0 := by
        apply Finset.sum_eq_zero
        intro b hb
        rw [expectationFrom_late test p n _ (by simp), mul_zero]
      rw [hs]
      simp only [add_zero, oneShot]
      split <;> simp_all [S.reward_one, S.reward_zero]

theorem expectationFrom_initial (test : S.Action → Bool) (p : SPolicy S) (n : ℕ) :
    expectationFrom p (embedEnvironment (oneShot test)) (n + 1) [] =
      firstTestProbability p test := by
  rw [expectationFrom_det_succ]
  simp only [oneShot, S.reward_zero, Int.cast_zero, zero_add, List.nil_append,
    expectationFrom_second]
  unfold firstTestProbability
  apply Finset.sum_congr rfl
  intro a ha
  split <;> simp_all

theorem finiteValue_eq_expectationFrom (p : SPolicy S) (μ : SEnvironment S) (n : ℕ) :
    finiteValue p μ (n + 1) = (expectationFrom p μ n [] : ℝ) := by
  simp [finiteValue, traceWeight, traceReward, expectationFrom, Trace,
    Rat.cast_sum, Rat.cast_mul]

theorem oneShotFiniteValue (S : Alphabet) : Targets.OneShotFiniteValue S := by
  intro test p n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  have he : 2 + k = (k + 1) + 1 := by omega
  rw [he, finiteValue_eq_expectationFrom, expectationFrom_initial]

theorem oneShot_tendsto (test : S.Action → Bool) (p : SPolicy S) :
    Tendsto (finiteValue p (embedEnvironment (oneShot test))) atTop
      (𝓝 (firstTestProbability p test : ℝ)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  exact (oneShotFiniteValue S test p n hn).symm

theorem oneShotAdmissible (S : Alphabet) : Targets.OneShotAdmissible S := by
  intro test
  exact ⟨fun p => ⟨_, oneShot_tendsto test (embedPolicy p)⟩,
    fun p => ⟨_, oneShot_tendsto test p⟩⟩

noncomputable def admissibleOneShot (test : S.Action → Bool) : AdmissibleDEnvironment S :=
  ⟨oneShot test, oneShotAdmissible S test⟩

theorem oneShot_value (test : S.Action → Bool) (p : SPolicy S) :
    value p (admissibleEmbedEnvironment (admissibleOneShot test)) =
      (firstTestProbability p test : ℝ) := by
  exact tendsto_nhds_unique
    (PolicySemanticsProof.valueLimit S p
      (admissibleEmbedEnvironment (admissibleOneShot test))).1
    (oneShot_tendsto test p)

theorem oneShotValue (S : Alphabet) : Targets.OneShotValue S := by
  intro test
  exact ⟨admissibleOneShot test, rfl, oneShot_value test,
    fun p => oneShot_value test (embedPolicy p)⟩

theorem test_eq_probability (a₀ : S.Action) (p : SPolicy S) :
    firstTestProbability p (eqTest a₀) = (p ([], S.zeroPercept)).mass a₀ := by
  classical
  simp [firstTestProbability, eqTest]

theorem test_neq_probability (a₀ : S.Action) (p : SPolicy S) :
    firstTestProbability p (neqTest a₀) = 1 - (p ([], S.zeroPercept)).mass a₀ := by
  classical
  have he : firstTestProbability p (neqTest a₀) + firstTestProbability p (eqTest a₀) = 1 := by
    unfold firstTestProbability
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ a : S.Action, (p ([], S.zeroPercept)).mass a := by
        apply Finset.sum_congr rfl
        intro a ha
        by_cases h : a = a₀ <;> simp [neqTest, eqTest, h]
      _ = 1 := Kernel.sum_one _
  rw [test_eq_probability] at he
  exact eq_sub_of_add_eq he

theorem oneShotSpecialValues (S : Alphabet) : Targets.OneShotSpecialValues S := by
  intro a₀
  refine ⟨admissibleOneShot (eqTest a₀), admissibleOneShot (neqTest a₀),
    admissibleOneShot falseTest, admissibleOneShot trueTest, rfl, rfl, rfl, rfl, ?_⟩
  intro p
  simp only [oneShot_value, test_eq_probability, test_neq_probability, Rat.cast_sub,
    Rat.cast_one]
  simp [firstTestProbability, falseTest, trueTest, Kernel.sum_one]

end LogicLineages.RL.Policy.OneShotProof
