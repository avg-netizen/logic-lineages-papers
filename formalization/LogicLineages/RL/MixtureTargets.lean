module

public import LogicLineages.RL.MixtureDefinitions

/-! Exact independent suppliers and complete source `lem:mixture`.
Finite identities quantify over all raw environments; only limiting values
use the previously frozen full all-policy admissibility definition. -/
@[expose] public section

namespace LogicLineages.RL.Policy.Targets

/-- Empty history and action extension laws for the literal action-only
product, including nonnegativity on every recorded off-path history. -/
def ActionLikelihoodLaw (S : Alphabet) : Prop :=
  ∀ p : SPolicy S, actionLikelihood p [] = 1 ∧
    (∀ h, 0 ≤ actionLikelihood p h) ∧
    (∀ (h : EnvHistory S) z a,
      actionLikelihood p (h ++ [(z, a)]) =
        actionLikelihood p h * (p (h, z)).mass a)

/-- The actual normalized kernel satisfies the printed rational quotient
formula at positive denominator and point-mass fallback at zero denominator. -/
def BehavioralMixtureRule (S : Alphabet) : Prop :=
  ∀ (a₀ : S.Action) (w : RatOpenUnit) (p q : SPolicy S) (h : AgentHistory S),
    (0 < mixtureDenominator w p q h.1 → ∀ a : S.Action,
      (behavioralMixture a₀ w p q h).mass a =
        (w.val * actionLikelihood p h.1 * (p h).mass a +
          (1 - w.val) * actionLikelihood q h.1 * (q h).mass a) /
          mixtureDenominator w p q h.1) ∧
    (mixtureDenominator w p q h.1 = 0 → behavioralMixture a₀ w p q h = dirac a₀)

/-- A zero denominator forces both nonnegative branch likelihoods to vanish;
no action extension can revive either branch or the denominator. -/
def MixtureZeroNoRevival (S : Alphabet) : Prop :=
  ∀ (w : RatOpenUnit) (p q : SPolicy S) (h : EnvHistory S),
    mixtureDenominator w p q h = 0 →
      actionLikelihood p h = 0 ∧ actionLikelihood q h = 0 ∧
      ∀ z a, actionLikelihood p (h ++ [(z, a)]) = 0 ∧
        actionLikelihood q (h ++ [(z, a)]) = 0 ∧
        mixtureDenominator w p q (h ++ [(z, a)]) = 0

/-- Complete mixture identity for action-only history likelihoods. -/
def BehavioralMixtureLikelihood (S : Alphabet) : Prop :=
  ∀ (a₀ : S.Action) (w : RatOpenUnit) (p q : SPolicy S) (h : EnvHistory S),
    actionLikelihood (behavioralMixture a₀ w p q) h =
      w.val * actionLikelihood p h + (1 - w.val) * actionLikelihood q h

/-- The environment likelihood is a common factor for every fixed full trace.
The zero horizon has both factors one; positive traces have no final action. -/
def TraceLikelihoodFactorization (S : Alphabet) : Prop :=
  ∀ (p : SPolicy S) (μ : SEnvironment S) (n : ℕ) (tr : Trace S n),
    traceWeight p μ n tr = tracePerceptLikelihood μ n tr *
      actionLikelihood p (traceCompletedHistory n tr)

def BehavioralMixtureTrace (S : Alphabet) : Prop :=
  ∀ (a₀ : S.Action) (w : RatOpenUnit) (p q : SPolicy S)
      (μ : SEnvironment S) (n : ℕ) (tr : Trace S n),
    traceWeight (behavioralMixture a₀ w p q) μ n tr =
      w.val * traceWeight p μ n tr + (1 - w.val) * traceWeight q μ n tr

def BehavioralMixtureFiniteValue (S : Alphabet) : Prop :=
  ∀ (a₀ : S.Action) (w : RatOpenUnit) (p q : SPolicy S)
      (μ : SEnvironment S) (n : ℕ),
    finiteValue (behavioralMixture a₀ w p q) μ n =
      (w.val : ℝ) * finiteValue p μ n + (1 - (w.val : ℝ)) * finiteValue q μ n

/-- Complete source `lem:mixture` in every actual admissible stochastic
 environment, with no additional normalization or effectiveness restriction. -/
def BehavioralMixtureValue (S : Alphabet) : Prop :=
  ∀ (a₀ : S.Action) (w : RatOpenUnit) (p q : SPolicy S)
      (μ : AdmissibleSEnvironment S),
    value (behavioralMixture a₀ w p q) μ =
      (w.val : ℝ) * value p μ + (1 - (w.val : ℝ)) * value q μ

def BehavioralMixtureDeterministicEnvironmentValue (S : Alphabet) : Prop :=
  ∀ (a₀ : S.Action) (w : RatOpenUnit) (p q : SPolicy S)
      (μ : AdmissibleDEnvironment S),
    value (behavioralMixture a₀ w p q) (admissibleEmbedEnvironment μ) =
      (w.val : ℝ) * value p (admissibleEmbedEnvironment μ) +
        (1 - (w.val : ℝ)) * value q (admissibleEmbedEnvironment μ)

end LogicLineages.RL.Policy.Targets
