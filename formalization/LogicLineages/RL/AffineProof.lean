module

public import LogicLineages.RL.PolicyTargets
public import Mathlib.Tactic.Ring

@[expose] public section

namespace LogicLineages.RL.Policy.AffineProof

open Filter Topology

/-- Once any completed round is recorded, all Q parameters prescribe the
same continuation, even at an off-path history. -/
theorem continuation_weight {S : Alphabet} (a₀ a₁ : S.Action)
    (t u : RatUnit) (μ : SEnvironment S) (n : ℕ) :
    ∀ h : EnvHistory S, h ≠ [] → ∀ tr : PositiveTrace S n,
      positiveWeight (firstActionMixture a₀ a₁ t) μ n h tr =
        positiveWeight (firstActionMixture a₀ a₁ u) μ n h tr := by
  induction n with
  | zero => intro h hh tr; rfl
  | succ n ih =>
      intro h hh tr
      rcases tr with ⟨z, a, rest⟩
      have he : h.isEmpty = false := by cases h <;> simp_all
      simp only [positiveWeight]
      rw [ih (h ++ [(z, a)]) (by simp) rest]
      simp [firstActionMixture, he]

theorem affineTraceLaw (S : Alphabet) : Targets.AffineTraceLaw S := by
  intro a₀ a₁ t μ n tr
  cases n with
  | zero => simp [traceWeight]
  | succ n =>
      cases n with
      | zero => simp [traceWeight, positiveWeight]; ring
      | succ n =>
          rcases tr with ⟨z, a, rest⟩
          simp only [traceWeight, positiveWeight, List.nil_append]
          rw [continuation_weight a₀ a₁ t zeroWeight μ n [(z, a)] (by simp) rest,
            continuation_weight a₀ a₁ oneWeight zeroWeight μ n [(z, a)] (by simp) rest]
          simp [firstActionMixture, kernelMix, zeroWeight, oneWeight]
          ring

theorem affineFiniteValue (S : Alphabet) : Targets.AffineFiniteValue S := by
  intro a₀ a₁ t μ n
  simp only [finiteValue]
  simp_rw [affineTraceLaw S a₀ a₁ t μ n, Rat.cast_add, Rat.cast_mul,
    Rat.cast_sub, Rat.cast_one, add_mul, mul_assoc]
  rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

theorem affineValue (S : Alphabet) : Targets.AffineValue S := by
  intro a₀ a₁ t μ
  have h₀ := Classical.choose_spec (μ.property.2 (firstActionMixture a₀ a₁ zeroWeight))
  have h₁ := Classical.choose_spec (μ.property.2 (firstActionMixture a₀ a₁ oneWeight))
  have ht := Classical.choose_spec (μ.property.2 (firstActionMixture a₀ a₁ t))
  change Tendsto _ atTop (𝓝 (value (firstActionMixture a₀ a₁ zeroWeight) μ)) at h₀
  change Tendsto _ atTop (𝓝 (value (firstActionMixture a₀ a₁ oneWeight) μ)) at h₁
  change Tendsto _ atTop (𝓝 (value (firstActionMixture a₀ a₁ t) μ)) at ht
  have hm := (h₀.const_mul (1 - (t.val : ℝ))).add (h₁.const_mul (t.val : ℝ))
  have he : (fun n => (1 - (t.val : ℝ)) *
      finiteValue (firstActionMixture a₀ a₁ zeroWeight) μ.val n +
      (t.val : ℝ) * finiteValue (firstActionMixture a₀ a₁ oneWeight) μ.val n) =
      finiteValue (firstActionMixture a₀ a₁ t) μ.val := by
    funext n
    exact (affineFiniteValue S a₀ a₁ t μ.val n).symm
  rw [he] at hm
  calc
    value (firstActionMixture a₀ a₁ t) μ =
        (1 - (t.val : ℝ)) * value (firstActionMixture a₀ a₁ zeroWeight) μ +
        (t.val : ℝ) * value (firstActionMixture a₀ a₁ oneWeight) μ :=
      tendsto_nhds_unique ht hm
    _ = _ := by ring

theorem affineDeterministicEnvironmentValue (S : Alphabet) :
    Targets.AffineDeterministicEnvironmentValue S := by
  intro a₀ a₁ t μ
  exact affineValue S a₀ a₁ t (admissibleEmbedEnvironment μ)

end LogicLineages.RL.Policy.AffineProof
