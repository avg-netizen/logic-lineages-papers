module

public import LogicLineages.RL.EnvironmentMixtureDefinitions

/-! Concrete suppliers for the source target-environment-mixture assumption.
All posterior and finite trace identities are unrestricted raw-kernel facts;
admissibility is derived for the full policy class, never added as an oracle. -/
@[expose] public section

namespace LogicLineages.RL.Policy.Targets

def PerceptHistoryLikelihoodLaw (S : Alphabet) : Prop :=
  ∀ μ : SEnvironment S, perceptHistoryLikelihood μ [] = 1 ∧
    (∀ h, 0 ≤ perceptHistoryLikelihood μ h) ∧
    (∀ (h : EnvHistory S) z a,
      perceptHistoryLikelihood μ (h ++ [(z, a)]) =
        perceptHistoryLikelihood μ h * (μ h).mass z)

def EnvironmentMixtureRule (S : Alphabet) : Prop :=
  ∀ (w : RatOpenUnit) (μ ν : SEnvironment S) (h : EnvHistory S),
    (0 < environmentMixtureDenominator w μ ν h → ∀ z : S.Percept,
      (environmentMixture w μ ν h).mass z =
        (w.val * perceptHistoryLikelihood μ h * (μ h).mass z +
          (1 - w.val) * perceptHistoryLikelihood ν h * (ν h).mass z) /
          environmentMixtureDenominator w μ ν h) ∧
    (environmentMixtureDenominator w μ ν h = 0 →
      environmentMixture w μ ν h = dirac S.zeroPercept)

def EnvironmentMixtureZeroNoRevival (S : Alphabet) : Prop :=
  ∀ (w : RatOpenUnit) (μ ν : SEnvironment S) (h : EnvHistory S),
    environmentMixtureDenominator w μ ν h = 0 →
      perceptHistoryLikelihood μ h = 0 ∧ perceptHistoryLikelihood ν h = 0 ∧
      ∀ z a, perceptHistoryLikelihood μ (h ++ [(z, a)]) = 0 ∧
        perceptHistoryLikelihood ν (h ++ [(z, a)]) = 0 ∧
        environmentMixtureDenominator w μ ν (h ++ [(z, a)]) = 0

/-- Terminal-percept likelihood identity on the original horizon types. -/
def EnvironmentMixturePerceptTrace (S : Alphabet) : Prop :=
  ∀ (w : RatOpenUnit) (μ ν : SEnvironment S) (n : ℕ) (tr : Trace S n),
    tracePerceptLikelihood (environmentMixture w μ ν) n tr =
      w.val * tracePerceptLikelihood μ n tr +
        (1 - w.val) * tracePerceptLikelihood ν n tr

def EnvironmentMixtureTrace (S : Alphabet) : Prop :=
  ∀ (w : RatOpenUnit) (μ ν : SEnvironment S) (p : SPolicy S)
      (n : ℕ) (tr : Trace S n),
    traceWeight p (environmentMixture w μ ν) n tr =
      w.val * traceWeight p μ n tr + (1 - w.val) * traceWeight p ν n tr

def EnvironmentMixtureFiniteValue (S : Alphabet) : Prop :=
  ∀ (w : RatOpenUnit) (μ ν : SEnvironment S) (p : SPolicy S) (n : ℕ),
    finiteValue p (environmentMixture w μ ν) n =
      (w.val : ℝ) * finiteValue p μ n + (1 - (w.val : ℝ)) * finiteValue p ν n

def EnvironmentMixtureAdmissible (S : Alphabet) : Prop :=
  ∀ (w : RatOpenUnit) (μ ν : AdmissibleSEnvironment S),
    Admissible (environmentMixture w μ.val ν.val)

/-- One actual admissible environment mixes both original environments for
all policies simultaneously, including embedded deterministic policies. -/
def EnvironmentMixtureValue (S : Alphabet) : Prop :=
  ∀ (w : RatOpenUnit) (μ ν : AdmissibleSEnvironment S),
    ∃ η : AdmissibleSEnvironment S, η.val = environmentMixture w μ.val ν.val ∧
      (∀ p : SPolicy S, value p η =
        (w.val : ℝ) * value p μ + (1 - (w.val : ℝ)) * value p ν) ∧
      (∀ p : DPolicy S, value (embedPolicy p) η =
        (w.val : ℝ) * value (embedPolicy p) μ + (1 - (w.val : ℝ)) * value (embedPolicy p) ν)

end LogicLineages.RL.Policy.Targets
