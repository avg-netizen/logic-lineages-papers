module

public import LogicLineages.RL.EnvironmentMixtureTargets
public import LogicLineages.RL.MixtureProof

@[expose] public section

namespace LogicLineages.RL.Policy.EnvironmentMixtureProof

open Filter Topology

variable {S : Alphabet}

theorem percept_empty (μ : SEnvironment S) : perceptHistoryLikelihood μ [] = 1 := by
  simp [perceptHistoryLikelihood]

theorem percept_nonneg (μ : SEnvironment S) (h : EnvHistory S) :
    0 ≤ perceptHistoryLikelihood μ h :=
  Finset.prod_nonneg (fun i _ => (μ (h.take i.val)).nonneg (h.get i).1)

theorem percept_snoc (μ : SEnvironment S) (h : EnvHistory S) (z : S.Percept) (a : S.Action) :
    perceptHistoryLikelihood μ (h ++ [(z, a)]) = perceptHistoryLikelihood μ h * (μ h).mass z := by
  unfold perceptHistoryLikelihood
  have hl : (h ++ [(z, a)]).length = h.length + 1 := by simp
  let f : Fin (h.length + 1) → ℚ := fun i =>
    (μ ((h ++ [(z, a)]).take i.val)).mass
      ((h ++ [(z, a)]).get ⟨i.val, by simpa [hl] using i.isLt⟩).1
  have he := Fintype.prod_equiv (finCongr hl)
    (fun i => (μ ((h ++ [(z, a)]).take i.val)).mass ((h ++ [(z, a)]).get i).1)
    f (fun i => rfl)
  rw [he, Fin.prod_univ_castSucc]
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    simp [f, List.get_eq_getElem, List.getElem_append, i.isLt,
      List.take_append_of_le_length (Nat.le_of_lt i.isLt)]
  · simp [f, List.get_eq_getElem, List.getElem_append]

theorem perceptHistoryLikelihoodLaw (S : Alphabet) : Targets.PerceptHistoryLikelihoodLaw S := by
  intro μ
  exact ⟨percept_empty μ, percept_nonneg μ, percept_snoc μ⟩

theorem denominator_nonneg (w : RatOpenUnit) (μ ν : SEnvironment S) (h : EnvHistory S) :
    0 ≤ environmentMixtureDenominator w μ ν h :=
  add_nonneg (mul_nonneg w.property.1.le (percept_nonneg μ h))
    (mul_nonneg (sub_nonneg.mpr w.property.2.le) (percept_nonneg ν h))

theorem environmentMixtureRule (S : Alphabet) : Targets.EnvironmentMixtureRule S := by
  intro w μ ν h
  constructor
  · intro hd z
    simp only [environmentMixture, hd, ↓reduceIte, kernelMix, environmentPosteriorWeight]
    simp only [↓reduceDIte]
    have hn := ne_of_gt hd
    field_simp
    unfold environmentMixtureDenominator
    ring
  · intro hd
    simp [environmentMixture, hd]

theorem environmentMixtureZeroNoRevival (S : Alphabet) : Targets.EnvironmentMixtureZeroNoRevival S := by
  intro w μ ν h hd
  have hp := percept_nonneg μ h
  have hq := percept_nonneg ν h
  have hwp : 0 ≤ w.val * perceptHistoryLikelihood μ h := mul_nonneg w.property.1.le hp
  have hwq : 0 ≤ (1 - w.val) * perceptHistoryLikelihood ν h :=
    mul_nonneg (sub_nonneg.mpr w.property.2.le) hq
  have hd' : w.val * perceptHistoryLikelihood μ h + (1 - w.val) * perceptHistoryLikelihood ν h = 0 := hd
  have hz₁ : w.val * perceptHistoryLikelihood μ h = 0 := by linarith
  have hz₂ : (1 - w.val) * perceptHistoryLikelihood ν h = 0 := by linarith
  have hpz : perceptHistoryLikelihood μ h = 0 :=
    (mul_eq_zero.mp hz₁).resolve_left (ne_of_gt w.property.1)
  have hqz : perceptHistoryLikelihood ν h = 0 :=
    (mul_eq_zero.mp hz₂).resolve_left (ne_of_gt (sub_pos.mpr w.property.2))
  refine ⟨hpz, hqz, ?_⟩
  intro z a
  simp [percept_snoc, hpz, hqz, environmentMixtureDenominator]

theorem weighted_step (w : RatOpenUnit) (μ ν : SEnvironment S) (h : EnvHistory S) (z : S.Percept) :
    environmentMixtureDenominator w μ ν h * (environmentMixture w μ ν h).mass z =
      w.val * perceptHistoryLikelihood μ h * (μ h).mass z +
        (1 - w.val) * perceptHistoryLikelihood ν h * (ν h).mass z := by
  by_cases hd : 0 < environmentMixtureDenominator w μ ν h
  · rw [(environmentMixtureRule S w μ ν h).1 hd z]
    exact mul_div_cancel₀ _ (ne_of_gt hd)
  · have hz : environmentMixtureDenominator w μ ν h = 0 :=
      le_antisymm (le_of_not_gt hd) (denominator_nonneg w μ ν h)
    obtain ⟨hp, hq, _⟩ := environmentMixtureZeroNoRevival S w μ ν h hz
    simp [hz, hp, hq]

/-- Includes the terminal percept's likelihood, without adding a final action.
The weighted identity is valid even when the entire prefix has zero weight. -/
theorem positive_weighted (w : RatOpenUnit) (μ ν : SEnvironment S) (n : ℕ) :
    ∀ h (tr : PositiveTrace S n),
      environmentMixtureDenominator w μ ν h *
        positivePerceptLikelihood (environmentMixture w μ ν) n h tr =
      w.val * perceptHistoryLikelihood μ h * positivePerceptLikelihood μ n h tr +
        (1 - w.val) * perceptHistoryLikelihood ν h * positivePerceptLikelihood ν n h tr := by
  induction n with
  | zero => intro h tr; exact weighted_step w μ ν h tr
  | succ n ih =>
      rintro h ⟨z, a, rest⟩
      have hs : environmentMixtureDenominator w μ ν h *
          (environmentMixture w μ ν h).mass z =
          environmentMixtureDenominator w μ ν (h ++ [(z, a)]) := by
        rw [weighted_step]
        simp only [environmentMixtureDenominator, percept_snoc]
        ring
      simp only [positivePerceptLikelihood]
      rw [← mul_assoc, hs, ih]
      simp only [percept_snoc]
      ring

theorem environmentMixturePerceptTrace (S : Alphabet) : Targets.EnvironmentMixturePerceptTrace S := by
  intro w μ ν n tr
  cases n with
  | zero => simp [tracePerceptLikelihood]
  | succ n =>
      have h := positive_weighted w μ ν n [] tr
      simpa [tracePerceptLikelihood, environmentMixtureDenominator, percept_empty] using h

theorem environmentMixtureTrace (S : Alphabet) : Targets.EnvironmentMixtureTrace S := by
  intro w μ ν p n tr
  rw [MixtureProof.traceLikelihoodFactorization S p (environmentMixture w μ ν),
    MixtureProof.traceLikelihoodFactorization S p μ,
    MixtureProof.traceLikelihoodFactorization S p ν, environmentMixturePerceptTrace S]
  ring

theorem environmentMixtureFiniteValue (S : Alphabet) : Targets.EnvironmentMixtureFiniteValue S := by
  intro w μ ν p n
  simp only [finiteValue]
  simp_rw [environmentMixtureTrace S w μ ν p n, Rat.cast_add, Rat.cast_mul,
    Rat.cast_sub, Rat.cast_one, add_mul, mul_assoc]
  rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

theorem mixture_tendsto (w : RatOpenUnit) (μ ν : AdmissibleSEnvironment S) (p : SPolicy S) :
    Tendsto (finiteValue p (environmentMixture w μ.val ν.val)) atTop
      (𝓝 ((w.val : ℝ) * value p μ + (1 - (w.val : ℝ)) * value p ν)) := by
  have hp := (PolicySemanticsProof.valueLimit S p μ).1
  have hq := (PolicySemanticsProof.valueLimit S p ν).1
  have hlim := (hp.const_mul (w.val : ℝ)).add (hq.const_mul (1 - (w.val : ℝ)))
  have he : (fun n => (w.val : ℝ) * finiteValue p μ.val n +
      (1 - (w.val : ℝ)) * finiteValue p ν.val n) =
      finiteValue p (environmentMixture w μ.val ν.val) := by
    funext n
    exact (environmentMixtureFiniteValue S w μ.val ν.val p n).symm
  rw [he] at hlim
  exact hlim

theorem environmentMixtureAdmissible (S : Alphabet) : Targets.EnvironmentMixtureAdmissible S := by
  intro w μ ν
  exact ⟨fun p => ⟨_, mixture_tendsto w μ ν (embedPolicy p)⟩,
    fun p => ⟨_, mixture_tendsto w μ ν p⟩⟩

noncomputable def admissibleEnvironmentMixture (w : RatOpenUnit)
    (μ ν : AdmissibleSEnvironment S) : AdmissibleSEnvironment S :=
  ⟨environmentMixture w μ.val ν.val, environmentMixtureAdmissible S w μ ν⟩

theorem environment_mixture_value (w : RatOpenUnit) (μ ν : AdmissibleSEnvironment S) (p : SPolicy S) :
    value p (admissibleEnvironmentMixture w μ ν) =
      (w.val : ℝ) * value p μ + (1 - (w.val : ℝ)) * value p ν := by
  exact tendsto_nhds_unique
    (PolicySemanticsProof.valueLimit S p (admissibleEnvironmentMixture w μ ν)).1
    (mixture_tendsto w μ ν p)

theorem environmentMixtureValue (S : Alphabet) : Targets.EnvironmentMixtureValue S := by
  intro w μ ν
  exact ⟨admissibleEnvironmentMixture w μ ν, rfl, environment_mixture_value w μ ν,
    fun p => environment_mixture_value w μ ν (embedPolicy p)⟩

end LogicLineages.RL.Policy.EnvironmentMixtureProof
