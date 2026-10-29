module

public import LogicLineages.RL.PolicyTargets
public import Mathlib.Data.Fintype.BigOperators
public import Lean.Elab.Tactic.Omega

@[expose] public section

namespace LogicLineages.RL.Policy.PolicySemanticsProof

open Filter Topology

variable {S : Alphabet}

theorem encodeEnv_injective : Function.Injective (@encodeEnv S) := by
  intro h
  induction h with
  | nil => intro k hk; cases k <;> simp_all [encodeEnv]
  | cons x h ih =>
      intro k hk
      rcases x with ⟨z, a⟩
      cases k with
      | nil => simp [encodeEnv] at hk
      | cons y k =>
          rcases y with ⟨w, b⟩
          simp only [encodeEnv, List.cons.injEq, Sum.inr.injEq, Sum.inl.injEq] at hk
          rcases hk with ⟨rfl, rfl, hk⟩
          exact congrArg (List.cons (z, a)) (ih hk)

theorem encodeAgent_injective : Function.Injective (@encodeAgent S) := by
  rintro ⟨h, z⟩ ⟨k, w⟩ hk
  induction h generalizing k z w with
  | nil =>
      cases k with
      | nil => simpa [encodeAgent, encodeEnv] using hk
      | cons x k => simp [encodeAgent, encodeEnv] at hk
  | cons x h ih =>
      rcases x with ⟨y, a⟩
      cases k with
      | nil => simp [encodeAgent, encodeEnv] at hk
      | cons x k =>
          rcases x with ⟨v, b⟩
          simp only [encodeAgent, encodeEnv, List.cons_append, List.cons.injEq,
            Sum.inr.injEq, Sum.inl.injEq] at hk
          rcases hk with ⟨rfl, rfl, hk⟩
          have hr := ih (k := k) (z := z) (w := w) hk
          cases hr
          rfl

theorem encodeEnv_valid (h : EnvHistory S) : IsEnvWord S (encodeEnv h) := by
  induction h with
  | nil => exact .nil
  | cons x h ih => exact .pair x.1 x.2 ih

theorem encodeAgent_valid (h : AgentHistory S) : IsAgentWord S (encodeAgent h) := by
  rcases h with ⟨h, z⟩
  induction h with
  | nil => exact .last z
  | cons x h ih => exact .pair x.1 x.2 ih

theorem envWord_surjective {w : List (Letter S)} (hw : IsEnvWord S w) :
    ∃ h, encodeEnv h = w := by
  induction hw with
  | nil => exact ⟨[], rfl⟩
  | pair z a hw ih =>
      obtain ⟨h, rfl⟩ := ih
      exact ⟨(z, a) :: h, rfl⟩

theorem agentWord_surjective {w : List (Letter S)} (hw : IsAgentWord S w) :
    ∃ h, encodeAgent h = w := by
  induction hw with
  | last z => exact ⟨([], z), rfl⟩
  | pair z a hw ih =>
      obtain ⟨⟨h, y⟩, rfl⟩ := ih
      exact ⟨((z, a) :: h, y), rfl⟩

theorem env_counts (h : EnvHistory S) :
    perceptCount (encodeEnv h) = h.length ∧ actionCount (encodeEnv h) = h.length := by
  induction h with
  | nil => simp [encodeEnv, perceptCount, actionCount]
  | cons x h ih =>
      rcases x with ⟨z, a⟩
      simpa [encodeEnv, perceptCount, actionCount] using ih

theorem agent_counts (h : AgentHistory S) :
    perceptCount (encodeAgent h) = h.1.length + 1 ∧
    actionCount (encodeAgent h) = h.1.length := by
  have hp := (env_counts h.1).1
  have ha := (env_counts h.1).2
  simpa [encodeAgent, perceptCount, actionCount] using And.intro hp ha

theorem historyCorrespondence (S : Alphabet) : Targets.HistoryCorrespondence S := by
  refine ⟨encodeEnv_injective, encodeAgent_injective, ?_, ?_, env_counts, agent_counts⟩
  · intro w
    constructor
    · rintro ⟨h, rfl⟩; exact encodeEnv_valid h
    · exact envWord_surjective
  · intro w
    constructor
    · rintro ⟨h, rfl⟩; exact encodeAgent_valid h
    · exact agentWord_surjective

theorem positiveWord_injective (n : ℕ) : Function.Injective (@positiveTraceWord S n) := by
  induction n with
  | zero =>
      intro x y h
      change @Eq S.Percept x y
      simpa [positiveTraceWord] using h
  | succ n ih =>
      rintro ⟨z, a, x⟩ ⟨w, b, y⟩ h
      simp only [positiveTraceWord, List.cons.injEq, Sum.inr.injEq, Sum.inl.injEq] at h
      rcases h with ⟨rfl, rfl, h⟩
      exact congrArg (fun x => (z, a, x)) (ih h)

theorem positiveWord_valid (n : ℕ) (tr : PositiveTrace S n) :
    IsAgentWord S (positiveTraceWord n tr) := by
  induction n with
  | zero => exact .last tr
  | succ n ih => exact .pair tr.1 tr.2.1 (ih tr.2.2)

theorem positiveWord_counts (n : ℕ) (tr : PositiveTrace S n) :
    perceptCount (positiveTraceWord n tr) = n + 1 ∧
    actionCount (positiveTraceWord n tr) = n ∧
    positiveReward n tr = literalReward (positiveTraceWord n tr) := by
  induction n with
  | zero => simp [positiveTraceWord, positiveReward, perceptCount, actionCount, literalReward]
  | succ n ih =>
      rcases tr with ⟨z, a, rest⟩
      have hr := ih rest
      simpa [positiveTraceWord, positiveReward, perceptCount, actionCount, literalReward,
        Nat.add_assoc] using hr

theorem agentWord_count_pos {w : List (Letter S)} (hw : IsAgentWord S w) :
    0 < perceptCount w := by
  induction hw with
  | last z => simp [perceptCount]
  | pair z a hw ih => simp [perceptCount] at *

theorem positiveWord_surjective (n : ℕ) (w : List (Letter S))
    (hw : IsAgentWord S w) (hc : perceptCount w = n + 1) :
    ∃ tr : PositiveTrace S n, positiveTraceWord n tr = w := by
  induction n generalizing w with
  | zero =>
      cases hw with
      | last z => exact ⟨z, rfl⟩
      | @pair z a w hw =>
          have hp := agentWord_count_pos hw
          change perceptCount w + 1 = 0 + 1 at hc
          omega
  | succ n ih =>
      cases hw with
      | last z => simp [perceptCount] at hc
      | @pair z a w hw =>
          have hc' : perceptCount w = n + 1 := by simpa [perceptCount] using hc
          obtain ⟨tr, rfl⟩ := ih w hw hc'
          exact ⟨(z, a, tr), rfl⟩

theorem traceCorrespondence (S : Alphabet) : Targets.TraceCorrespondence S := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n
    cases n with
    | zero =>
        intro x y _
        change @Eq Unit x y
        exact @Subsingleton.elim Unit inferInstance x y
    | succ n => exact positiveWord_injective n
  · intro w
    constructor
    · rintro ⟨tr, rfl⟩; rfl
    · rintro rfl; exact ⟨(), rfl⟩
  · intro n w
    constructor
    · rintro ⟨tr, rfl⟩
      exact ⟨positiveWord_valid n tr, (positiveWord_counts n tr).1⟩
    · rintro ⟨hw, hc⟩
      exact positiveWord_surjective n w hw hc
  · intro n tr
    cases n with
    | zero => simp [traceWord, traceReward, perceptCount, actionCount, literalReward]
    | succ n => simpa [traceWord, traceReward] using positiveWord_counts n tr

theorem positiveWeight_nonneg (p : SPolicy S) (μ : SEnvironment S) (n : ℕ) :
    ∀ h (tr : PositiveTrace S n), 0 ≤ positiveWeight p μ n h tr := by
  induction n with
  | zero => intro h tr; exact (μ h).nonneg tr
  | succ n ih =>
      intro h tr
      exact mul_nonneg (mul_nonneg ((μ h).nonneg tr.1)
        ((p (h, tr.1)).nonneg tr.2.1)) (ih _ tr.2.2)

theorem positiveWeight_sum (p : SPolicy S) (μ : SEnvironment S) (n : ℕ) :
    ∀ h, (∑ tr : PositiveTrace S n, positiveWeight p μ n h tr) = 1 := by
  induction n with
  | zero => intro h; exact (μ h).sum_one
  | succ n ih =>
      intro h
      change (∑ tr : S.Percept × S.Action × PositiveTrace S n,
        (μ h).mass tr.1 * (p (h, tr.1)).mass tr.2.1 *
          positiveWeight p μ n (h ++ [(tr.1, tr.2.1)]) tr.2.2) = 1
      simp only [Fintype.sum_prod_type, ← Finset.mul_sum, ih, mul_one, Kernel.sum_one]

theorem positiveWeight_literal (p : SPolicy S) (μ : SEnvironment S) (n : ℕ) :
    ∀ h (tr : PositiveTrace S n),
      positiveWeight p μ n h tr = literalWeight p μ h (positiveTraceWord n tr) := by
  induction n with
  | zero => intro h tr; rfl
  | succ n ih =>
      rintro h ⟨z, a, rest⟩
      simp only [positiveTraceWord, literalWeight, positiveWeight, ih]

theorem finiteTraceLaw (S : Alphabet) : Targets.FiniteTraceLaw S := by
  intro p μ n
  cases n with
  | zero => simp [traceWeight, traceWord, literalWeight, Trace]
  | succ n =>
      exact ⟨positiveWeight_nonneg p μ n [], positiveWeight_sum p μ n [],
        positiveWeight_literal p μ n []⟩

theorem deterministic_weight (p : DPolicy S) (μ : DEnvironment S) (n : ℕ) :
    ∀ h (tr : PositiveTrace S n),
      positiveWeight (embedPolicy p) (embedEnvironment μ) n h tr =
        (dirac (deterministicTrace p μ n h)).mass tr := by
  classical
  induction n with
  | zero => intro h tr; rfl
  | succ n ih =>
      rintro h ⟨z, a, rest⟩
      simp only [positiveWeight, deterministicTrace]
      rw [ih]
      by_cases hz : z = μ h
      · subst z
        by_cases ha : a = p (h, μ h)
        · subst a; simp [embedPolicy, embedEnvironment, dirac, PositiveTrace, Prod.mk.injEq]
        · simp [embedPolicy, embedEnvironment, dirac, PositiveTrace, Prod.mk.injEq, ha]
      · simp [embedPolicy, embedEnvironment, dirac, PositiveTrace, Prod.mk.injEq, hz]

theorem deterministicCalibration (S : Alphabet) : Targets.DeterministicCalibration S := by
  classical
  refine ⟨?_, ?_, deterministic_weight, ?_⟩
  · intro p h
    simp [embedPolicy, dirac]
  · intro μ h
    simp [embedEnvironment, dirac]
  · intro p μ n
    change (∑ tr : PositiveTrace S n,
      (positiveWeight (embedPolicy p) (embedEnvironment μ) n [] tr : ℝ) *
      (positiveReward n tr : ℝ)) = _
    simp_rw [deterministic_weight]
    simp [dirac, apply_ite]

theorem initialHorizonCalibration (S : Alphabet) : Targets.InitialHorizonCalibration S := by
  intro p μ
  constructor
  · simp [finiteValue, traceWeight, traceReward, Trace]
  · rfl

theorem valueLimit (S : Alphabet) : Targets.ValueLimit S := by
  intro p μ
  have h : Tendsto (finiteValue p μ.val) atTop (𝓝 (value p μ)) :=
    Classical.choose_spec (μ.property.2 p)
  exact ⟨h, fun v hv => tendsto_nhds_unique hv h⟩

theorem kernel_ext {X : Type} [Fintype X] {k l : Kernel X}
    (h : ∀ x, k.mass x = l.mass x) : k = l := by
  cases k
  cases l
  congr
  exact funext h

theorem firstActionPolicy (S : Alphabet) : Targets.FirstActionPolicy S := by
  intro a₀ a₁
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext h
    apply kernel_ext
    intro a
    by_cases he : h.1.isEmpty = true
    · simp [firstActionMixture, he, kernelMix, zeroWeight, embedPolicy, constantPolicy]
    · simp [firstActionMixture, he, embedPolicy, constantPolicy]
  · funext h
    apply kernel_ext
    intro a
    by_cases he : h.1.isEmpty = true
    · simp [firstActionMixture, he, kernelMix, oneWeight, embedPolicy, firstThenPolicy]
    · simp [firstActionMixture, he, embedPolicy, firstThenPolicy]
  · intro t z a
    rfl
  · intro t h z hh
    have he : h.isEmpty = false := by cases h <;> simp_all
    simp [firstActionMixture, he]

end LogicLineages.RL.Policy.PolicySemanticsProof
