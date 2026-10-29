module

public import LogicLineages.RL.MixtureTargets
public import LogicLineages.RL.PolicySemanticsProof
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.List.Induction
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace LogicLineages.RL.Policy.MixtureProof

open Filter Topology

variable {S : Alphabet}

theorem likelihood_empty (p : SPolicy S) : actionLikelihood p [] = 1 := by
  simp [actionLikelihood]

theorem likelihood_nonneg (p : SPolicy S) (h : EnvHistory S) : 0 ≤ actionLikelihood p h :=
  Finset.prod_nonneg (fun i _ => (p (h.take i.val, (h.get i).1)).nonneg (h.get i).2)

theorem likelihood_snoc (p : SPolicy S) (h : EnvHistory S) (z : S.Percept) (a : S.Action) :
    actionLikelihood p (h ++ [(z, a)]) = actionLikelihood p h * (p (h, z)).mass a := by
  unfold actionLikelihood
  have hl : (h ++ [(z, a)]).length = h.length + 1 := by simp
  let f : Fin (h.length + 1) → ℚ := fun i =>
    (p ((h ++ [(z, a)]).take i.val,
      ((h ++ [(z, a)]).get ⟨i.val, by simpa [hl] using i.isLt⟩).1)).mass
      ((h ++ [(z, a)]).get ⟨i.val, by simpa [hl] using i.isLt⟩).2
  have he := Fintype.prod_equiv (finCongr hl)
    (fun i => (p ((h ++ [(z, a)]).take i.val, ((h ++ [(z, a)]).get i).1)).mass
      ((h ++ [(z, a)]).get i).2) f (fun i => rfl)
  rw [he, Fin.prod_univ_castSucc]
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    simp [f, List.get_eq_getElem, List.getElem_append, i.isLt,
      List.take_append_of_le_length (Nat.le_of_lt i.isLt)]
  · simp [f, List.get_eq_getElem, List.getElem_append]

theorem actionLikelihoodLaw (S : Alphabet) : Targets.ActionLikelihoodLaw S := by
  intro p
  exact ⟨likelihood_empty p, likelihood_nonneg p, likelihood_snoc p⟩

theorem denominator_nonneg (w : RatOpenUnit) (p q : SPolicy S) (h : EnvHistory S) :
    0 ≤ mixtureDenominator w p q h :=
  add_nonneg (mul_nonneg w.property.1.le (likelihood_nonneg p h))
    (mul_nonneg (sub_nonneg.mpr w.property.2.le) (likelihood_nonneg q h))

theorem behavioralMixtureRule (S : Alphabet) : Targets.BehavioralMixtureRule S := by
  intro a₀ w p q h
  constructor
  · intro hd a
    simp only [behavioralMixture, hd, ↓reduceIte, kernelMix, posteriorWeight]
    simp only [hd, ↓reduceDIte]
    have hn := ne_of_gt hd
    field_simp
    unfold mixtureDenominator
    ring
  · intro hd
    simp [behavioralMixture, hd]

theorem mixtureZeroNoRevival (S : Alphabet) : Targets.MixtureZeroNoRevival S := by
  intro w p q h hd
  have hp := likelihood_nonneg p h
  have hq := likelihood_nonneg q h
  have hwp : 0 ≤ w.val * actionLikelihood p h := mul_nonneg w.property.1.le hp
  have hwq : 0 ≤ (1 - w.val) * actionLikelihood q h :=
    mul_nonneg (sub_nonneg.mpr w.property.2.le) hq
  have hd' : w.val * actionLikelihood p h + (1 - w.val) * actionLikelihood q h = 0 := hd
  have hz₁ : w.val * actionLikelihood p h = 0 := by linarith
  have hz₂ : (1 - w.val) * actionLikelihood q h = 0 := by linarith
  have hpz : actionLikelihood p h = 0 :=
    (mul_eq_zero.mp hz₁).resolve_left (ne_of_gt w.property.1)
  have hqz : actionLikelihood q h = 0 :=
    (mul_eq_zero.mp hz₂).resolve_left (ne_of_gt (sub_pos.mpr w.property.2))
  refine ⟨hpz, hqz, ?_⟩
  intro z a
  simp [likelihood_snoc, hpz, hqz, mixtureDenominator]

theorem behavioralMixtureLikelihood (S : Alphabet) : Targets.BehavioralMixtureLikelihood S := by
  intro a₀ w p q h
  induction h using List.reverseRecOn with
  | nil => simp [likelihood_empty]
  | append_singleton h x ih =>
      rcases x with ⟨z, a⟩
      rw [likelihood_snoc, likelihood_snoc, likelihood_snoc, ih]
      by_cases hd : 0 < mixtureDenominator w p q h
      · rw [(behavioralMixtureRule S a₀ w p q (h, z)).1 hd a]
        have hn := ne_of_gt hd
        change mixtureDenominator w p q h * (_ / mixtureDenominator w p q h) = _
        rw [mul_div_cancel₀ _ hn]
        ring
      · have hz : mixtureDenominator w p q h = 0 :=
          le_antisymm (le_of_not_gt hd) (denominator_nonneg w p q h)
        obtain ⟨hp, hq, _⟩ := mixtureZeroNoRevival S w p q h hz
        simp [hp, hq]

/-- General-history factorization avoids dividing by an action likelihood;
it remains valid when the entire prefix has probability zero. -/
theorem positive_factorization (p : SPolicy S) (μ : SEnvironment S) (n : ℕ) :
    ∀ h (tr : PositiveTrace S n),
      positiveWeight p μ n h tr * actionLikelihood p h =
        positivePerceptLikelihood μ n h tr *
          actionLikelihood p (h ++ positiveCompletedHistory n tr) := by
  induction n with
  | zero => intro h tr; simp [positiveWeight, positivePerceptLikelihood, positiveCompletedHistory]
  | succ n ih =>
      rintro h ⟨z, a, rest⟩
      simp only [positiveWeight, positivePerceptLikelihood, positiveCompletedHistory]
      have ht := ih (h ++ [(z, a)]) rest
      rw [likelihood_snoc] at ht
      have hl : (h ++ [(z, a)]) ++ positiveCompletedHistory n rest =
          h ++ ((z, a) :: positiveCompletedHistory n rest) := by simp [List.append_assoc]
      rw [hl] at ht
      calc
        (μ h).mass z * (p (h, z)).mass a *
            positiveWeight p μ n (h ++ [(z, a)]) rest * actionLikelihood p h =
          (μ h).mass z * (positiveWeight p μ n (h ++ [(z, a)]) rest *
            (actionLikelihood p h * (p (h, z)).mass a)) := by ring
        _ = (μ h).mass z * (positivePerceptLikelihood μ n (h ++ [(z, a)]) rest *
            actionLikelihood p (h ++ ((z, a) :: positiveCompletedHistory n rest))) := by rw [ht]
        _ = _ := by ring

theorem traceLikelihoodFactorization (S : Alphabet) : Targets.TraceLikelihoodFactorization S := by
  intro p μ n tr
  cases n with
  | zero => simp [traceWeight, tracePerceptLikelihood, traceCompletedHistory, likelihood_empty]
  | succ n =>
      have h := positive_factorization p μ n [] tr
      simpa [traceWeight, tracePerceptLikelihood, traceCompletedHistory, likelihood_empty] using h

theorem behavioralMixtureTrace (S : Alphabet) : Targets.BehavioralMixtureTrace S := by
  intro a₀ w p q μ n tr
  rw [traceLikelihoodFactorization S (behavioralMixture a₀ w p q),
    traceLikelihoodFactorization S p, traceLikelihoodFactorization S q,
    behavioralMixtureLikelihood S]
  ring

theorem behavioralMixtureFiniteValue (S : Alphabet) : Targets.BehavioralMixtureFiniteValue S := by
  intro a₀ w p q μ n
  simp only [finiteValue]
  simp_rw [behavioralMixtureTrace S a₀ w p q μ n, Rat.cast_add, Rat.cast_mul,
    Rat.cast_sub, Rat.cast_one, add_mul, mul_assoc]
  rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

theorem behavioralMixtureValue (S : Alphabet) : Targets.BehavioralMixtureValue S := by
  intro a₀ w p q μ
  have hp := (PolicySemanticsProof.valueLimit S p μ).1
  have hq := (PolicySemanticsProof.valueLimit S q μ).1
  have hm := (PolicySemanticsProof.valueLimit S (behavioralMixture a₀ w p q) μ).1
  have hlim := (hp.const_mul (w.val : ℝ)).add (hq.const_mul (1 - (w.val : ℝ)))
  have he : (fun n => (w.val : ℝ) * finiteValue p μ.val n +
      (1 - (w.val : ℝ)) * finiteValue q μ.val n) =
      finiteValue (behavioralMixture a₀ w p q) μ.val := by
    funext n
    exact (behavioralMixtureFiniteValue S a₀ w p q μ.val n).symm
  rw [he] at hlim
  exact tendsto_nhds_unique hm hlim

theorem behavioralMixtureDeterministicEnvironmentValue (S : Alphabet) :
    Targets.BehavioralMixtureDeterministicEnvironmentValue S := by
  intro a₀ w p q μ
  exact behavioralMixtureValue S a₀ w p q (admissibleEmbedEnvironment μ)

end LogicLineages.RL.Policy.MixtureProof
