module

public import LogicLineages.RL.PositiveTransformationTargets
public import LogicLineages.RL.OneShotProof
public import LogicLineages.RL.AffineProof
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace LogicLineages.RL.Policy.PositiveTransformationProof

open OneShotProof

variable {S : Alphabet}

def statistic (a₀ : S.Action) (p : SPolicy S) : RatUnit :=
  ⟨(p ([], S.zeroPercept)).mass a₀, (p ([], S.zeroPercept)).nonneg a₀, by
    have h := Finset.single_le_sum
      (fun a (_ : a ∈ (Finset.univ : Finset S.Action)) =>
        (p ([], S.zeroPercept)).nonneg a) (Finset.mem_univ a₀)
    simpa only [Kernel.sum_one] using h⟩

noncomputable def liftPolicy : (k : Kind) → DPolicy S → Agent S k
  | .deterministic, p => p
  | .stochastic, p => embedPolicy p

noncomputable def liftEnvironment : (k : Kind) → AdmissibleDEnvironment S → Environment S k
  | .deterministic, μ => μ
  | .stochastic, μ => admissibleEmbedEnvironment μ

theorem liftPolicy_kernel (k : Kind) (p : DPolicy S) :
    agentKernel k (liftPolicy k p) = embedPolicy p := by cases k <;> rfl

theorem liftEnvironment_kernel (k : Kind) (μ : AdmissibleDEnvironment S) :
    environmentKernel k (liftEnvironment k μ) = admissibleEmbedEnvironment μ := by
  cases k <;> rfl

noncomputable def deterministicImage (a₀ a₁ : S.Action) (p : DPolicy S) : DPolicy S := by
  classical
  exact if p ([], S.zeroPercept) = a₀ then firstThenPolicy a₀ a₁ else constantPolicy a₀

/-- The unused S→D case is irrelevant to the conditional theorem; the D→D
case uses genuine deterministic endpoints, not a stochastic codomain. -/
noncomputable def imageAgent (a₀ a₁ : S.Action) :
    (source target : Kind) → Agent S source → Agent S target
  | .deterministic, .deterministic, p => deterministicImage a₀ a₁ p
  | .stochastic, .deterministic, _ => constantPolicy a₀
  | source, .stochastic, p => firstActionMixture a₀ a₁ (statistic a₀ (agentKernel source p))

theorem imageAgent_kernel (a₀ a₁ : S.Action) (source target : Kind)
    (allowed : source = .deterministic ∨ target = .stochastic) (p : Agent S source) :
    agentKernel target (imageAgent a₀ a₁ source target p) =
      firstActionMixture a₀ a₁ (statistic a₀ (agentKernel source p)) := by
  classical
  cases source <;> cases target
  · by_cases h : p ([], S.zeroPercept) = a₀
    · have ht : statistic a₀ (embedPolicy p) = oneWeight := by
        apply Subtype.ext
        simp [statistic, embedPolicy, dirac, h, oneWeight]
      change embedPolicy (deterministicImage a₀ a₁ p) =
        firstActionMixture a₀ a₁ (statistic a₀ (embedPolicy p))
      rw [ht]
      simpa [deterministicImage, h] using
        (PolicySemanticsProof.firstActionPolicy S a₀ a₁).2.1.symm
    · have ht : statistic a₀ (embedPolicy p) = zeroWeight := by
        apply Subtype.ext
        simp [statistic, embedPolicy, dirac, h, Ne.symm h, zeroWeight]
      change embedPolicy (deterministicImage a₀ a₁ p) =
        firstActionMixture a₀ a₁ (statistic a₀ (embedPolicy p))
      rw [ht]
      simpa [deterministicImage, h] using
        (PolicySemanticsProof.firstActionPolicy S a₀ a₁).1.symm
  · rfl
  · simp at allowed
  · rfl

noncomputable def rankingEnvironment (a₀ a₁ : S.Action)
    (μ : AdmissibleSEnvironment S) : AdmissibleDEnvironment S := by
  classical
  exact if value (firstActionMixture a₀ a₁ zeroWeight) μ <
      value (firstActionMixture a₀ a₁ oneWeight) μ then admissibleOneShot (eqTest a₀)
    else if value (firstActionMixture a₀ a₁ oneWeight) μ <
      value (firstActionMixture a₀ a₁ zeroWeight) μ then admissibleOneShot (neqTest a₀)
    else admissibleOneShot falseTest

theorem affine_rank (a₀ a₁ : S.Action) (p q : SPolicy S)
    (μ : AdmissibleSEnvironment S) :
    (value (firstActionMixture a₀ a₁ (statistic a₀ p)) μ <
      value (firstActionMixture a₀ a₁ (statistic a₀ q)) μ) ↔
    (value p (admissibleEmbedEnvironment (rankingEnvironment a₀ a₁ μ)) <
      value q (admissibleEmbedEnvironment (rankingEnvironment a₀ a₁ μ))) := by
  classical
  rw [AffineProof.affineValue S a₀ a₁ (statistic a₀ p) μ,
    AffineProof.affineValue S a₀ a₁ (statistic a₀ q) μ]
  let A := value (firstActionMixture a₀ a₁ zeroWeight) μ
  let B := value (firstActionMixture a₀ a₁ oneWeight) μ
  by_cases hp : A < B
  · simp only [rankingEnvironment, show value (firstActionMixture a₀ a₁ zeroWeight) μ <
        value (firstActionMixture a₀ a₁ oneWeight) μ from hp, ↓reduceIte,
      oneShot_value, test_eq_probability]
    exact add_lt_add_iff_left A |>.trans (mul_lt_mul_iff_left₀ (sub_pos.mpr hp))
  · by_cases hn : B < A
    · simp only [rankingEnvironment, show ¬(value (firstActionMixture a₀ a₁ zeroWeight) μ <
          value (firstActionMixture a₀ a₁ oneWeight) μ) from hp,
        show value (firstActionMixture a₀ a₁ oneWeight) μ <
          value (firstActionMixture a₀ a₁ zeroWeight) μ from hn, ↓reduceIte,
        oneShot_value, test_neq_probability, Rat.cast_sub, Rat.cast_one]
      change (A + ((p ([], S.zeroPercept)).mass a₀ : ℝ) * (B - A) <
        A + ((q ([], S.zeroPercept)).mass a₀ : ℝ) * (B - A)) ↔ _
      have he := (mul_lt_mul_iff_left₀ (sub_pos.mpr hn) :
        ((q ([], S.zeroPercept)).mass a₀ : ℝ) * (A - B) <
          ((p ([], S.zeroPercept)).mass a₀ : ℝ) * (A - B) ↔
        ((q ([], S.zeroPercept)).mass a₀ : ℝ) < ((p ([], S.zeroPercept)).mass a₀ : ℝ))
      constructor
      · intro h
        have h' := he.mp (by nlinarith)
        linarith
      · intro h
        have h' := he.mpr (by linarith)
        nlinarith
    · have he : B = A := le_antisymm (le_of_not_gt hp) (le_of_not_gt hn)
      simp only [rankingEnvironment, show ¬(value (firstActionMixture a₀ a₁ zeroWeight) μ <
          value (firstActionMixture a₀ a₁ oneWeight) μ) from hp,
        show ¬(value (firstActionMixture a₀ a₁ oneWeight) μ <
          value (firstActionMixture a₀ a₁ zeroWeight) μ) from hn, ↓reduceIte,
        oneShot_value]
      change (A + _ * (B - A) < A + _ * (B - A)) ↔ _
      simp [he, firstTestProbability, falseTest]

theorem image_value_oneShot (a₀ a₁ : S.Action) (source target envKind : Kind)
    (allowed : source = .deterministic ∨ target = .stochastic)
    (p : Agent S source) (test : S.Action → Bool) :
    (framework S target envKind).value (imageAgent a₀ a₁ source target p)
      (liftEnvironment envKind (admissibleOneShot test)) =
      (firstTestProbability (firstActionMixture a₀ a₁
        (statistic a₀ (agentKernel source p))) test : ℝ) := by
  change value (agentKernel target (imageAgent a₀ a₁ source target p))
    (environmentKernel envKind (liftEnvironment envKind (admissibleOneShot test))) = _
  rw [imageAgent_kernel a₀ a₁ source target allowed p, liftEnvironment_kernel, oneShot_value]

theorem statistic_constant_self (a₀ : S.Action) :
    statistic a₀ (embedPolicy (constantPolicy a₀)) = oneWeight := by
  classical
  apply Subtype.ext
  simp [statistic, embedPolicy, constantPolicy, dirac, oneWeight]

theorem statistic_constant_other (a₀ a₁ : S.Action) (hne : a₀ ≠ a₁) :
    statistic a₀ (embedPolicy (constantPolicy a₁)) = zeroWeight := by
  classical
  apply Subtype.ext
  simp [statistic, embedPolicy, constantPolicy, dirac, hne, zeroWeight]

theorem positiveTransformation (S : Alphabet) : Targets.PositiveTransformation S := by
  classical
  intro source sourceEnv target targetEnv hex allowed
  obtain ⟨a₀, a₁, hne⟩ := hex
  refine ⟨{
    agentMap := imageAgent a₀ a₁ source target
    environmentMap := fun μ => liftEnvironment sourceEnv
      (rankingEnvironment a₀ a₁ (environmentKernel targetEnv μ))
    faithful := ?_
    agentsSeparated := ?_
    environmentVaries := ?_
  }⟩
  · intro p q μ
    change (value (agentKernel target (imageAgent a₀ a₁ source target p))
        (environmentKernel targetEnv μ) <
      value (agentKernel target (imageAgent a₀ a₁ source target q))
        (environmentKernel targetEnv μ)) ↔ _
    rw [imageAgent_kernel a₀ a₁ source target allowed p,
      imageAgent_kernel a₀ a₁ source target allowed q]
    change _ ↔ (value (agentKernel source p)
      (environmentKernel sourceEnv (liftEnvironment sourceEnv
        (rankingEnvironment a₀ a₁ (environmentKernel targetEnv μ)))) <
      value (agentKernel source q)
        (environmentKernel sourceEnv (liftEnvironment sourceEnv
          (rankingEnvironment a₀ a₁ (environmentKernel targetEnv μ)))))
    rw [liftEnvironment_kernel]
    exact affine_rank a₀ a₁ _ _ _
  · refine ⟨liftPolicy source (constantPolicy a₁), liftPolicy source (constantPolicy a₀),
      liftEnvironment targetEnv (admissibleOneShot (eqTest a₁)), ?_⟩
    rw [image_value_oneShot a₀ a₁ source target targetEnv allowed,
      image_value_oneShot a₀ a₁ source target targetEnv allowed,
      liftPolicy_kernel, liftPolicy_kernel, statistic_constant_other a₀ a₁ hne,
      statistic_constant_self, test_eq_probability, test_eq_probability]
    simp [firstActionMixture, kernelMix, zeroWeight, oneWeight, dirac, Ne.symm hne]
  · refine ⟨liftPolicy source (constantPolicy a₀),
      liftEnvironment targetEnv (admissibleOneShot falseTest),
      liftEnvironment targetEnv (admissibleOneShot trueTest), ?_⟩
    rw [image_value_oneShot a₀ a₁ source target targetEnv allowed,
      image_value_oneShot a₀ a₁ source target targetEnv allowed]
    simp [firstTestProbability, falseTest, trueTest, Kernel.sum_one]

end LogicLineages.RL.Policy.PositiveTransformationProof
