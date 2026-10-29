module

public import LogicLineages.RL.CrossDefinitions

/-! General lattice-sequence suppliers, actual-framework calibrations, and
full source cross-order obstruction. The final general source target uses
convergent per-step lattice reward traces, not an assumed value oracle. -/
@[expose] public section

namespace LogicLineages.RL.Policy.Targets

open Filter Topology

def LatticeLimit (d : PositiveDenominator) : Prop :=
  ∀ (f : ℕ → ℝ) (v : ℝ), (∀ n, ∃ z : ℤ, f n = (z : ℝ) / (d.val : ℝ)) →
    Tendsto f atTop (𝓝 v) → ∃ z : ℤ, v = (z : ℝ) / (d.val : ℝ)

/-- Arbitrary signed per-step lattice rewards, with no boundedness/rate/finite
support assumption: convergence of their actual totals forces a lattice value. -/
def LatticeRewardLimit (d : PositiveDenominator) : Prop :=
  ∀ (rewards : ℕ → ℝ) (v : ℝ),
    (∀ n, ∃ z : ℤ, rewards n = (z : ℝ) / (d.val : ℝ)) →
    Tendsto (fun n => ∑ i ∈ Finset.range n, rewards i) atTop (𝓝 v) →
    ∃ z : ℤ, v = (z : ℝ) / (d.val : ℝ)

def DeterministicRewardLattice (F : LogicLineages.RL.Framework)
    (d : PositiveDenominator) : Prop :=
  DeterministicLatticeRewards F d → LatticeValued F d

def DDIntegerValue (S : Alphabet) : Prop :=
  ∀ (p : DPolicy S) (μ : AdmissibleDEnvironment S),
    ∃ z : ℤ, value (embedPolicy p) (admissibleEmbedEnvironment μ) = (z : ℝ)

def ScaledDDCalibration (S : Alphabet) (d : PositiveDenominator) : Prop :=
  LatticeValued (scaledDD S d) d ∧
  ∀ (p : DPolicy S) (μ : AdmissibleDEnvironment S),
    Tendsto (scaledFiniteValue p μ d) atTop (𝓝 ((scaledDD S d).value p μ)) ∧
    ∀ n, scaledFiniteValue p μ d n =
      ∑ tr : Trace S n, (traceWeight (embedPolicy p) (embedEnvironment μ.val) n tr : ℝ) *
        ((traceReward n tr : ℝ) / (d.val : ℝ))

def ActualFrameworkEnvironmentMixtures (S : Alphabet) : Prop :=
  ∀ agents : Kind, RationalEnvironmentMixtures (framework S agents Kind.stochastic)

/-- Abstract order component only. Not a full-source claim until the reward
trace-to-lattice and actual mixture suppliers have been checked. -/
def CrossOrderObstruction : Prop :=
  ∀ (F G : LogicLineages.RL.Framework) (d : PositiveDenominator),
    LatticeValued F d → RationalEnvironmentMixtures G → NoCrossWithVariation F G

/-- Full source `prop:cross` with its general deterministic reward-trace domain
and only the second nontriviality condition. No integer-alphabet rescaling
restriction is substituted for arbitrary fixed-lattice reward sequences. -/
def CrossFromDeterministicRewards : Prop :=
  ∀ (F G : LogicLineages.RL.Framework) (d : PositiveDenominator),
    DeterministicLatticeRewards F d → RationalEnvironmentMixtures G →
      NoCrossWithVariation F G

/-- Concrete actual-policy specialization, allowing different source and
target alphabets. This is a calibration, not exhaustive source-domain coverage. -/
def ActualScaledDDCrossObstruction : Prop :=
  ∀ (S T : Alphabet) (d : PositiveDenominator) (targetAgents : Kind),
    NoCrossWithVariation (scaledDD S d) (framework T targetAgents Kind.stochastic)

end LogicLineages.RL.Policy.Targets
