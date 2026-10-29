module

public import LogicLineages.RL.MixtureDefinitions

/-! Paper 13 `eq:cross` and `prop:cross`. The general deterministic source
representation includes actual per-pair reward streams and convergence of
their partial sums to values. Scaled DD is a calibration, not the entire
source domain. No common bound, convergence rate, or finite reward support
is imposed on these arbitrary signed lattice reward streams. -/
@[expose] public section

namespace LogicLineages.RL.Policy

abbrev PositiveDenominator := {d : ℕ // 0 < d}

def CrossFaithful (F G : LogicLineages.RL.Framework) (f : F.Agent → G.Agent)
    (g : G.Environment → F.Environment) : Prop :=
  ∀ p q μ ν, G.value (f p) μ < G.value (f q) ν ↔ F.value p (g μ) < F.value q (g ν)

def NoCrossWithVariation (F G : LogicLineages.RL.Framework) : Prop :=
  ¬ ∃ (f : F.Agent → G.Agent) (g : G.Environment → F.Environment),
    CrossFaithful F G f g ∧ LogicLineages.RL.EnvironmentVaries G f

def LatticeValued (F : LogicLineages.RL.Framework) (d : PositiveDenominator) : Prop :=
  ∀ p μ, ∃ z : ℤ, F.value p μ = (z : ℝ) / (d.val : ℝ)

/-- Exactly the source's target initial-mixture assumption, at the value level;
separate concrete environment-mixture targets derive it from actual kernels. -/
def RationalEnvironmentMixtures (G : LogicLineages.RL.Framework) : Prop :=
  ∀ (μ ν : G.Environment) (w : RatOpenUnit), ∃ η : G.Environment,
    ∀ p : G.Agent, G.value p η =
      (w.val : ℝ) * G.value p μ + (1 - (w.val : ℝ)) * G.value p ν

open Filter Topology

/-- Arbitrary deterministic per-pair reward traces with precisely the source
lattice and convergence hypotheses. No lattice-value conclusion is assumed. -/
def DeterministicLatticeRewards (F : LogicLineages.RL.Framework)
    (d : PositiveDenominator) : Prop :=
  ∃ rewards : F.Agent → F.Environment → ℕ → ℝ,
    (∀ p μ n, ∃ z : ℤ, rewards p μ n = (z : ℝ) / (d.val : ℝ)) ∧
    ∀ p μ, Tendsto (fun n => ∑ i ∈ Finset.range n, rewards p μ i)
      atTop (𝓝 (F.value p μ))

noncomputable def scaledFramework (F : LogicLineages.RL.Framework)
    (d : PositiveDenominator) : LogicLineages.RL.Framework where
  Agent := F.Agent
  Environment := F.Environment
  value p μ := F.value p μ / (d.val : ℝ)

noncomputable def scaledDD (S : Alphabet) (d : PositiveDenominator) :
    LogicLineages.RL.Framework :=
  scaledFramework (framework S Kind.deterministic Kind.deterministic) d

noncomputable def scaledFiniteValue {S : Alphabet} (p : DPolicy S)
    (μ : AdmissibleDEnvironment S) (d : PositiveDenominator) (n : ℕ) : ℝ :=
  finiteValue (embedPolicy p) (embedEnvironment μ.val) n / (d.val : ℝ)

end LogicLineages.RL.Policy
