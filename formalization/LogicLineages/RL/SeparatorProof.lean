module

public import LogicLineages.RL.SeparatorTargets
public import LogicLineages.RL.OneShotProof
public import LogicLineages.RL.MixtureProof
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace LogicLineages.RL.Policy.SeparatorProof

open Filter Topology OneShotProof

variable {S : Alphabet}

attribute [local instance] Classical.propDecidable

theorem historyFrom_append (p : DPolicy S) (ys zs : List S.Percept) :
    ∀ h, scriptHistoryFrom p h (ys ++ zs) =
      scriptHistoryFrom p (scriptHistoryFrom p h ys) zs := by
  induction ys with
  | nil => intro h; rfl
  | cons z ys ih => intro h; exact ih _

theorem historyFrom_length (p : DPolicy S) (ys : List S.Percept) :
    ∀ h, (scriptHistoryFrom p h ys).length = h.length + ys.length := by
  induction ys with
  | nil => intro h; simp [scriptHistoryFrom]
  | cons z ys ih =>
      intro h
      rw [scriptHistoryFrom, ih]
      simp; omega

theorem historyFrom_percepts (p : DPolicy S) (ys : List S.Percept) :
    ∀ h, (scriptHistoryFrom p h ys).map Prod.fst = h.map Prod.fst ++ ys := by
  induction ys with
  | nil => intro h; simp [scriptHistoryFrom]
  | cons z ys ih =>
      intro h
      rw [scriptHistoryFrom, ih]
      simp [List.append_assoc]

theorem history_snoc (p : DPolicy S) (ys : List S.Percept) (z : S.Percept) :
    scriptHistory p (ys ++ [z]) = scriptHistory p ys ++ [(z, p (scriptHistory p ys, z))] := by
  simp [scriptHistory, historyFrom_append, scriptHistoryFrom]

theorem scriptHistoryLaw (S : Alphabet) : Targets.ScriptHistoryLaw S := by
  intro p ys
  exact ⟨by simpa [scriptHistory] using historyFrom_length p ys [],
    by simpa [scriptHistory] using historyFrom_percepts p ys [], history_snoc p ys⟩

theorem deterministic_likelihood (p : DPolicy S) (h : EnvHistory S) :
    actionLikelihood (embedPolicy p) h =
      if h = scriptHistory p (h.map Prod.fst) then 1 else 0 := by
  classical
  induction h using List.reverseRecOn with
  | nil => simp [MixtureProof.likelihood_empty, scriptHistory, scriptHistoryFrom]
  | append_singleton h x ih =>
      rcases x with ⟨z, a⟩
      rw [MixtureProof.likelihood_snoc, ih]
      simp only [List.map_append, List.map_singleton, history_snoc]
      by_cases he : h = scriptHistory p (h.map Prod.fst)
      · have hr := he.symm
        simp [hr, embedPolicy, dirac, Prod.mk.injEq]
      · have hn : h ++ [(z, a)] ≠ scriptHistory p (h.map Prod.fst) ++
            [(z, p (scriptHistory p (h.map Prod.fst), z))] := by
          intro hx
          apply he
          have hd := congrArg List.dropLast hx
          simpa using hd
        simp [he, hn]

theorem scriptTraceExtensionality (S : Alphabet) : Targets.ScriptTraceExtensionality S := by
  intro p q he μ n tr
  rw [MixtureProof.traceLikelihoodFactorization S, MixtureProof.traceLikelihoodFactorization S]
  rw [deterministic_likelihood, deterministic_likelihood, he]

theorem valueDistinctionDivergence (S : Alphabet) : Targets.ValueDistinctionDivergence S := by
  classical
  intro p q μ hne
  by_contra hn
  have hno : ∀ ys, ¬ FirstDivergence p q ys := fun ys hy => hn ⟨ys, hy⟩
  have hh : ∀ ys, scriptHistory p ys = scriptHistory q ys := by
    intro ys
    induction ys using List.reverseRecOn with
    | nil => rfl
    | append_singleton ys z ih =>
        have ha : p (scriptHistory p ys, z) = q (scriptHistory q ys, z) := by
          by_contra ha
          exact hno (ys ++ [z]) ⟨ys, z, rfl, ih, ha⟩
        rw [history_snoc, history_snoc, ha, ih]
  have hv : finiteValue (embedPolicy p) μ.val = finiteValue (embedPolicy q) μ.val := by
    funext n
    unfold finiteValue
    apply Finset.sum_congr rfl
    intro tr htr
    rw [scriptTraceExtensionality S p q hh μ.val n tr]
  have hp := (PolicySemanticsProof.valueLimit S (embedPolicy p) μ).1
  rw [hv] at hp
  exact hne (tendsto_nhds_unique hp (PolicySemanticsProof.valueLimit S (embedPolicy q) μ).1)

theorem scriptedSeparatorOffPathRule (S : Alphabet) : Targets.ScriptedSeparatorOffPathRule S := by
  classical
  intro ys bs
  refine ⟨?_, ?_, ?_⟩
  · intro h hl; simp [scriptedSeparator, hl]
  · intro h he; simp [scriptedSeparator, he]
  · intro h hl
    have hn : ¬ h.length < ys.length := by omega
    have he : h.length ≠ ys.length := by omega
    simp [scriptedSeparator, hn, he]

theorem expectation_zero_tail (μ : DEnvironment S) (N : ℕ) (hz : RewardZeroAfter μ N)
    (p : SPolicy S) (n : ℕ) :
    ∀ h : EnvHistory S, N ≤ h.length → expectationFrom p (embedEnvironment μ) n h = 0 := by
  induction n with
  | zero => intro h hh; rw [expectationFrom_det_zero, hz h hh]; simp
  | succ n ih =>
      intro h hh
      rw [expectationFrom_det_succ, hz h hh]
      simp only [Int.cast_zero, zero_add]
      apply Finset.sum_eq_zero
      intro a ha
      rw [ih _ (by simp; omega), mul_zero]

theorem expectation_stable (μ : DEnvironment S) (N : ℕ) (hz : RewardZeroAfter μ N)
    (p : SPolicy S) (n : ℕ) :
    ∀ (k : ℕ) (h : EnvHistory S), N ≤ h.length + n + 1 →
      expectationFrom p (embedEnvironment μ) (n + k) h =
        expectationFrom p (embedEnvironment μ) n h := by
  induction n with
  | zero =>
      intro k h hn
      cases k with
      | zero => rfl
      | succ k =>
          rw [Nat.zero_add, expectationFrom_det_succ, expectationFrom_det_zero]
          have hs : (∑ a : S.Action, (p (h, μ h)).mass a *
              expectationFrom p (embedEnvironment μ) k (h ++ [(μ h, a)])) = 0 := by
            apply Finset.sum_eq_zero
            intro a ha
            rw [expectation_zero_tail μ N hz p k _ (by simpa using hn), mul_zero]
          rw [hs, add_zero]
  | succ n ih =>
      intro k h hn
      have he : n + 1 + k = (n + k) + 1 := by omega
      rw [he, expectationFrom_det_succ, expectationFrom_det_succ]
      congr 1
      apply Finset.sum_congr rfl
      intro a ha
      rw [ih k _ (by simp; omega)]

theorem finite_tail_stable (μ : DEnvironment S) (N : ℕ) (hz : RewardZeroAfter μ N)
    (p : SPolicy S) (n : ℕ) (hn : N ≤ n) :
    finiteValue p (embedEnvironment μ) n = finiteValue p (embedEnvironment μ) N := by
  cases N with
  | zero =>
      cases n with
      | zero => rfl
      | succ n =>
          rw [finiteValue_eq_expectationFrom, expectation_zero_tail μ 0 hz p n [] (by simp)]
          simp [(PolicySemanticsProof.initialHorizonCalibration S p (embedEnvironment μ)).1]
  | succ N =>
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
      have he : N + 1 + k = (N + k) + 1 := by omega
      rw [he, finiteValue_eq_expectationFrom, finiteValue_eq_expectationFrom,
        expectation_stable μ (N + 1) hz p N k [] (by simp)]

theorem finite_tail_tendsto (μ : DEnvironment S) (N : ℕ) (hz : RewardZeroAfter μ N)
    (p : SPolicy S) : Tendsto (finiteValue p (embedEnvironment μ)) atTop
      (𝓝 (finiteValue p (embedEnvironment μ) N)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop N] with n hn
  exact (finite_tail_stable μ N hz p n hn).symm

theorem finiteRewardTail (S : Alphabet) : Targets.FiniteRewardTail S := by
  intro μ N hz
  refine ⟨fun p n hn => finite_tail_stable μ N hz p n hn, ?_⟩
  exact ⟨fun p => ⟨_, finite_tail_tendsto μ N hz (embedPolicy p)⟩,
    fun p => ⟨_, finite_tail_tendsto μ N hz p⟩⟩

theorem scripted_tail (ys : List S.Percept) (bs : List S.Action) :
    RewardZeroAfter (scriptedSeparator ys bs) (ys.length + 1) := by
  intro h hh
  rw [(scriptedSeparatorOffPathRule S ys bs).2.2 h (by omega), S.reward_zero]

theorem scriptedSeparatorAdmissible (S : Alphabet) : Targets.ScriptedSeparatorAdmissible S := by
  intro ys bs
  exact ⟨scripted_tail ys bs, (finiteRewardTail S _ _ (scripted_tail ys bs)).2⟩

noncomputable def admissibleSeparator (ys : List S.Percept) (bs : List S.Action) :
    AdmissibleDEnvironment S := ⟨scriptedSeparator ys bs, (scriptedSeparatorAdmissible S ys bs).2⟩

theorem separator_value_finite (ys : List S.Percept) (bs : List S.Action) (p : SPolicy S) :
    value p (admissibleEmbedEnvironment (admissibleSeparator ys bs)) =
      finiteValue p (embedEnvironment (scriptedSeparator ys bs)) (ys.length + 1) := by
  exact tendsto_nhds_unique
    (PolicySemanticsProof.valueLimit S p (admissibleEmbedEnvironment (admissibleSeparator ys bs))).1
    (finite_tail_tendsto _ _ (scripted_tail ys bs) p)

/-- The next scripted percept does not depend on any recorded action. -/
theorem scripted_next (seen rest : List S.Percept) (z : S.Percept) (bs : List S.Action)
    (h : EnvHistory S) (hh : h.length = seen.length) :
    scriptedSeparator (seen ++ z :: rest) bs h = z := by
  classical
  have hl : h.length < (seen ++ z :: rest).length := by simp; omega
  rw [(scriptedSeparatorOffPathRule S _ bs).1 h hl]
  simp [List.get_eq_getElem, List.getElem_append, hh]

theorem deterministic_script_reward (p : DPolicy S) (ys : List S.Percept)
    (bs : List S.Action) :
    ∀ (seen : List S.Percept) (h : EnvHistory S), h.length = seen.length →
      positiveReward ys.length
        (deterministicTrace p (scriptedSeparator (seen ++ ys) bs) ys.length h) =
      scriptReward ys + if (scriptHistoryFrom p h ys).map Prod.snd = bs then 1 else 0 := by
  classical
  induction ys with
  | nil =>
      intro seen h hh
      simp only [List.length_nil, deterministicTrace, positiveReward, scriptHistoryFrom,
        List.append_nil, scriptReward, List.map_nil, List.sum_nil, zero_add]
      rw [(scriptedSeparatorOffPathRule S seen bs).2.1 h hh]
      split <;> simp_all [S.reward_one, S.reward_zero]
  | cons z ys ih =>
      intro seen h hh
      have hnext := scripted_next seen ys z bs h hh
      simp only [List.length_cons, deterministicTrace, positiveReward]
      rw [hnext]
      have he : seen ++ z :: ys = (seen ++ [z]) ++ ys := by simp [List.append_assoc]
      rw [he, ih (seen ++ [z]) (h ++ [(z, p (h, z))]) (by simp [hh])]
      simp [scriptReward, scriptHistoryFrom, add_assoc]

theorem scriptedSeparatorDeterministicValue (S : Alphabet) :
    Targets.ScriptedSeparatorDeterministicValue S := by
  classical
  intro ys bs
  refine ⟨admissibleSeparator ys bs, rfl, ?_⟩
  intro p
  rw [separator_value_finite, (PolicySemanticsProof.deterministicCalibration S).2.2.2]
  have h := deterministic_script_reward p ys bs [] [] (by simp)
  simp only [List.nil_append] at h
  rw [h]
  simp [scriptActions, scriptHistory, Int.cast_add, apply_ite]

/-- Rational bounds for the actual stochastic expectation after any consumed
script prefix. The script reward is identical on every action branch. -/
theorem stochastic_script_bounds (p : SPolicy S) (ys : List S.Percept) (bs : List S.Action) :
    ∀ (seen : List S.Percept) (h : EnvHistory S), h.length = seen.length →
      (scriptReward ys : ℚ) ≤ expectationFrom p
        (embedEnvironment (scriptedSeparator (seen ++ ys) bs)) ys.length h ∧
      expectationFrom p (embedEnvironment (scriptedSeparator (seen ++ ys) bs)) ys.length h ≤
        (scriptReward ys : ℚ) + 1 := by
  classical
  induction ys with
  | nil =>
      intro seen h hh
      rw [List.length_nil, expectationFrom_det_zero]
      simp only [List.append_nil]
      rw [(scriptedSeparatorOffPathRule S seen bs).2.1 h hh]
      split <;> simp [scriptReward, S.reward_one, S.reward_zero]
  | cons z ys ih =>
      intro seen h hh
      rw [List.length_cons, expectationFrom_det_succ, scripted_next seen ys z bs h hh]
      have he : seen ++ z :: ys = (seen ++ [z]) ++ ys := by simp [List.append_assoc]
      have hlo : (scriptReward ys : ℚ) ≤
          ∑ a : S.Action, (p (h, z)).mass a *
            expectationFrom p (embedEnvironment (scriptedSeparator (seen ++ z :: ys) bs))
              ys.length (h ++ [(z, a)]) := by
        calc
          (scriptReward ys : ℚ) = ∑ a : S.Action, (p (h, z)).mass a * (scriptReward ys : ℚ) := by
            rw [← Finset.sum_mul, Kernel.sum_one, one_mul]
          _ ≤ _ := by
            apply Finset.sum_le_sum
            intro a ha
            apply mul_le_mul_of_nonneg_left _ ((p (h, z)).nonneg a)
            rw [he]
            exact (ih (seen ++ [z]) (h ++ [(z, a)]) (by simp [hh])).1
      have hhi : (∑ a : S.Action, (p (h, z)).mass a *
            expectationFrom p (embedEnvironment (scriptedSeparator (seen ++ z :: ys) bs))
              ys.length (h ++ [(z, a)])) ≤ (scriptReward ys : ℚ) + 1 := by
        calc
          _ ≤ ∑ a : S.Action, (p (h, z)).mass a * ((scriptReward ys : ℚ) + 1) := by
            apply Finset.sum_le_sum
            intro a ha
            apply mul_le_mul_of_nonneg_left _ ((p (h, z)).nonneg a)
            rw [he]
            exact (ih (seen ++ [z]) (h ++ [(z, a)]) (by simp [hh])).2
          _ = _ := by rw [← Finset.sum_mul, Kernel.sum_one, one_mul]
      simp only [scriptReward, List.map_cons, List.sum_cons, Int.cast_add] at hlo hhi ⊢
      constructor <;> linarith

theorem scriptedSeparatorStochasticBounds (S : Alphabet) :
    Targets.ScriptedSeparatorStochasticBounds S := by
  intro ys bs
  refine ⟨admissibleSeparator ys bs, rfl, ?_⟩
  intro p
  rw [separator_value_finite, finiteValue_eq_expectationFrom]
  have h := stochastic_script_bounds p ys bs [] [] (by simp)
  simp only [List.nil_append] at h
  constructor
  · exact_mod_cast h.1
  · exact_mod_cast h.2

theorem divergence_actions_ne (p q : DPolicy S) (ys : List S.Percept)
    (hd : FirstDivergence p q ys) : scriptActions q ys ≠ scriptActions p ys := by
  obtain ⟨prior, z, rfl, hh, ha⟩ := hd
  intro he
  simp only [scriptActions, history_snoc, List.map_append, List.map_singleton] at he
  rw [← hh] at he
  have he' : q (scriptHistory p prior, z) = p (scriptHistory p prior, z) := by simpa using he
  apply ha
  simpa [hh] using he'.symm

theorem firstDivergenceSeparator (S : Alphabet) : Targets.FirstDivergenceSeparator S := by
  classical
  intro p q ys hd
  obtain ⟨e, he, hv⟩ := scriptedSeparatorDeterministicValue S ys (scriptActions p ys)
  refine ⟨e, he, ?_, ?_⟩
  · simpa using hv p
  · simpa [divergence_actions_ne p q ys hd] using hv q

theorem twoValueSeparator (S : Alphabet) : Targets.TwoValueSeparator S := by
  classical
  intro p q μ hne
  obtain ⟨ys, hd⟩ := valueDistinctionDivergence S p q μ hne
  obtain ⟨e, he, hv⟩ := scriptedSeparatorDeterministicValue S ys (scriptActions p ys)
  refine ⟨e, scriptReward ys, ?_, ?_⟩
  · intro r
    by_cases hr : scriptActions r ys = scriptActions p ys
    · exact Or.inr (by simpa [hr] using hv r)
    · exact Or.inl (by simpa [hr] using hv r)
  · have hp : value (embedPolicy p) (admissibleEmbedEnvironment e) = (scriptReward ys : ℝ) + 1 := by
      simpa using hv p
    have hq : value (embedPolicy q) (admissibleEmbedEnvironment e) = (scriptReward ys : ℝ) := by
      simpa [divergence_actions_ne p q ys hd] using hv q
    rw [hp, hq]
    linarith

end LogicLineages.RL.Policy.SeparatorProof
