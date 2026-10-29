module

public import LogicLineages.RL.InteractionDefinitions

/-! Independent source-comparison targets for paper 13. These are specifications,
not accepted results. Semantic foundations and the affine component are staged
separately from the still-pending separator, behavioral mixture and classification. -/
@[expose] public section

namespace LogicLineages.RL.Policy.Targets

open Filter Topology

/-- Typed histories cover exactly the literal alternating histories, including
all off-path histories, without quotienting policies by on-path behavior. -/
def HistoryCorrespondence (S : Alphabet) : Prop :=
  Function.Injective (@encodeEnv S) ∧
  Function.Injective (@encodeAgent S) ∧
  (∀ w, (∃ h, encodeEnv h = w) ↔ IsEnvWord S w) ∧
  (∀ w, (∃ h, encodeAgent h = w) ↔ IsAgentWord S w) ∧
  (∀ h : EnvHistory S, perceptCount (encodeEnv h) = h.length ∧
    actionCount (encodeEnv h) = h.length) ∧
  (∀ h : AgentHistory S, perceptCount (encodeAgent h) = h.1.length + 1 ∧
    actionCount (encodeAgent h) = h.1.length)

/-- Exact horizon convention: first n percepts, no final action, empty at zero.
Surjectivity is onto an independently defined literal-word grammar. -/
def TraceCorrespondence (S : Alphabet) : Prop :=
  (∀ n, Function.Injective (@traceWord S n)) ∧
  (∀ w, (∃ tr : Trace S 0, traceWord 0 tr = w) ↔ w = []) ∧
  (∀ n w, (∃ tr : Trace S (n + 1), traceWord (n + 1) tr = w) ↔
    IsAgentWord S w ∧ perceptCount w = n + 1) ∧
  (∀ n (tr : Trace S n), perceptCount (traceWord n tr) = n ∧
    actionCount (traceWord n tr) = n - 1 ∧
    traceReward n tr = literalReward (traceWord n tr))

/-- Actual normalized trace probabilities and correspondence to the literal
alternating kernel recursion, for arbitrary (not necessarily admissible) μ. -/
def FiniteTraceLaw (S : Alphabet) : Prop :=
  ∀ (p : SPolicy S) (μ : SEnvironment S) (n : ℕ),
    (∀ tr : Trace S n, 0 ≤ traceWeight p μ n tr) ∧
    (∑ tr : Trace S n, traceWeight p μ n tr) = 1 ∧
    (∀ tr : Trace S n,
      traceWeight p μ n tr = literalWeight p μ [] (traceWord n tr))

/-- Point masses really are deterministic objects, and deterministic
interaction gives the recursively generated trace and reward. -/
def DeterministicCalibration (S : Alphabet) : Prop :=
  (∀ (p : DPolicy S) h, (embedPolicy p h).mass (p h) = 1 ∧
    ∀ a, a ≠ p h → (embedPolicy p h).mass a = 0) ∧
  (∀ (μ : DEnvironment S) h, (embedEnvironment μ h).mass (μ h) = 1 ∧
    ∀ z, z ≠ μ h → (embedEnvironment μ h).mass z = 0) ∧
  (∀ (p : DPolicy S) (μ : DEnvironment S) n h (tr : PositiveTrace S n),
    positiveWeight (embedPolicy p) (embedEnvironment μ) n h tr =
      (dirac (deterministicTrace p μ n h)).mass tr) ∧
  (∀ (p : DPolicy S) (μ : DEnvironment S) n,
    finiteValue (embedPolicy p) (embedEnvironment μ) (n + 1) =
      (positiveReward n (deterministicTrace p μ n []) : ℝ))

/-- Boundary calibration is independent of the policy and retains the initial
percept reward. It rules out both an omitted initial reward and a final action. -/
def InitialHorizonCalibration (S : Alphabet) : Prop :=
  ∀ (p : SPolicy S) (μ : SEnvironment S),
    finiteValue p μ 0 = 0 ∧
    finiteValue p μ 1 =
      ∑ z : S.Percept, ((μ []).mass z : ℝ) * (S.reward z : ℝ)

/-- The selected value is the unique finite real limit of the actual finite
expectations, not a free value field on environments. -/
def ValueLimit (S : Alphabet) : Prop :=
  ∀ (p : SPolicy S) (μ : AdmissibleSEnvironment S),
    Tendsto (finiteValue p μ.val) atTop (𝓝 (value p μ)) ∧
    ∀ v : ℝ, Tendsto (finiteValue p μ.val) atTop (𝓝 v) → v = value p μ

/-- Endpoints are actual point-mass deterministic policies; no distinct-action
assumption is needed for this component. -/
def FirstActionPolicy (S : Alphabet) : Prop :=
  ∀ a₀ a₁ : S.Action,
    firstActionMixture a₀ a₁ zeroWeight = embedPolicy (constantPolicy a₀) ∧
    firstActionMixture a₀ a₁ oneWeight = embedPolicy (firstThenPolicy a₀ a₁) ∧
    (∀ (t : RatUnit) z a,
      (firstActionMixture a₀ a₁ t ([], z)).mass a =
        (1 - t.val) * (dirac a₀).mass a + t.val * (dirac a₁).mass a) ∧
    (∀ (t : RatUnit) h z, h ≠ [] →
      firstActionMixture a₀ a₁ t (h, z) = dirac a₀)

/-- Finite-horizon trace mixture: no admissibility or environment assumption. -/
def AffineTraceLaw (S : Alphabet) : Prop :=
  ∀ (a₀ a₁ : S.Action) (t : RatUnit) (μ : SEnvironment S)
      (n : ℕ) (tr : Trace S n),
    traceWeight (firstActionMixture a₀ a₁ t) μ n tr =
      (1 - t.val) * traceWeight (firstActionMixture a₀ a₁ zeroWeight) μ n tr +
        t.val * traceWeight (firstActionMixture a₀ a₁ oneWeight) μ n tr

/-- Finite-sum consequence, before any limit or admissibility is used. -/
def AffineFiniteValue (S : Alphabet) : Prop :=
  ∀ (a₀ a₁ : S.Action) (t : RatUnit) (μ : SEnvironment S) (n : ℕ),
    finiteValue (firstActionMixture a₀ a₁ t) μ n =
      (1 - (t.val : ℝ)) * finiteValue (firstActionMixture a₀ a₁ zeroWeight) μ n +
        (t.val : ℝ) * finiteValue (firstActionMixture a₀ a₁ oneWeight) μ n

/-- Full source `lem:affine` over admissible stochastic environments;
deterministic environments are included by their actual point-mass embeddings. -/
def AffineValue (S : Alphabet) : Prop :=
  ∀ (a₀ a₁ : S.Action) (t : RatUnit) (μ : AdmissibleSEnvironment S),
    value (firstActionMixture a₀ a₁ t) μ =
      value (firstActionMixture a₀ a₁ zeroWeight) μ +
        (t.val : ℝ) * (value (firstActionMixture a₀ a₁ oneWeight) μ -
          value (firstActionMixture a₀ a₁ zeroWeight) μ)

/-- Explicit D-environment specialization of the same source lemma. -/
def AffineDeterministicEnvironmentValue (S : Alphabet) : Prop :=
  ∀ (a₀ a₁ : S.Action) (t : RatUnit) (μ : AdmissibleDEnvironment S),
    value (firstActionMixture a₀ a₁ t) (admissibleEmbedEnvironment μ) =
      value (firstActionMixture a₀ a₁ zeroWeight) (admissibleEmbedEnvironment μ) +
        (t.val : ℝ) *
          (value (firstActionMixture a₀ a₁ oneWeight) (admissibleEmbedEnvironment μ) -
            value (firstActionMixture a₀ a₁ zeroWeight) (admissibleEmbedEnvironment μ))

end LogicLineages.RL.Policy.Targets
