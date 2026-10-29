module

public import LogicLineages.RL.SeparatorDefinitions

/-! Independent actual-domain separator suppliers and full source lemma.
No finite-divergence, normalization, admissibility, or two-value conclusion
is introduced as an oracle premise of the final separator target. -/
@[expose] public section

namespace LogicLineages.RL.Policy.Targets

def ScriptHistoryLaw (S : Alphabet) : Prop :=
  ∀ (p : DPolicy S) (ys : List S.Percept),
    (scriptHistory p ys).length = ys.length ∧
    (scriptHistory p ys).map Prod.fst = ys ∧
    ∀ z, scriptHistory p (ys ++ [z]) =
      scriptHistory p ys ++ [(z, p (scriptHistory p ys, z))]

/-- Equal responses to every prescribed percept sequence force equality of
actual finite trace laws even in history-dependent stochastic environments. -/
def ScriptTraceExtensionality (S : Alphabet) : Prop :=
  ∀ (p q : DPolicy S), (∀ ys, scriptHistory p ys = scriptHistory q ys) →
    ∀ (μ : SEnvironment S) (n : ℕ) (tr : Trace S n),
      traceWeight (embedPolicy p) μ n tr = traceWeight (embedPolicy q) μ n tr

/-- Derive an actual finite first divergence from unequal limiting values. -/
def ValueDistinctionDivergence (S : Alphabet) : Prop :=
  ∀ (p q : DPolicy S) (μ : AdmissibleSEnvironment S),
    value (embedPolicy p) μ ≠ value (embedPolicy q) μ →
      ∃ ys : List S.Percept, FirstDivergence p q ys

def ScriptedSeparatorOffPathRule (S : Alphabet) : Prop := by
  classical
  exact ∀ (ys : List S.Percept) (bs : List S.Action),
    (∀ (h : EnvHistory S) (hl : h.length < ys.length),
      scriptedSeparator ys bs h = ys.get ⟨h.length, hl⟩) ∧
    (∀ h : EnvHistory S, h.length = ys.length →
      scriptedSeparator ys bs h = if h.map Prod.snd = bs then S.onePercept else S.zeroPercept) ∧
    (∀ h : EnvHistory S, ys.length < h.length → scriptedSeparator ys bs h = S.zeroPercept)

/-- Generic finite-tail supplier, to be proved from actual trace expectations.
It does not assert that arbitrary admissible environments have finite support. -/
def FiniteRewardTail (S : Alphabet) : Prop :=
  ∀ (μ : DEnvironment S) (N : ℕ), RewardZeroAfter μ N →
    (∀ (p : SPolicy S) (n : ℕ), N ≤ n →
      finiteValue p (embedEnvironment μ) n = finiteValue p (embedEnvironment μ) N) ∧
    Admissible (embedEnvironment μ)

def ScriptedSeparatorAdmissible (S : Alphabet) : Prop :=
  ∀ (ys : List S.Percept) (bs : List S.Action),
    RewardZeroAfter (scriptedSeparator ys bs) (ys.length + 1) ∧
    Admissible (embedEnvironment (scriptedSeparator ys bs))

/-- Exact deterministic value formula, stronger than merely lying between the
endpoints. The same packaged environment serves every deterministic policy. -/
def ScriptedSeparatorDeterministicValue (S : Alphabet) : Prop := by
  classical
  exact ∀ (ys : List S.Percept) (bs : List S.Action),
    ∃ e : AdmissibleDEnvironment S, e.val = scriptedSeparator ys bs ∧
      ∀ p : DPolicy S, value (embedPolicy p) (admissibleEmbedEnvironment e) =
        (scriptReward ys : ℝ) + if scriptActions p ys = bs then 1 else 0

/-- Separate stochastic interval supplier; it is not a replacement for the
exact universal deterministic two-value range in the final separator lemma. -/
def ScriptedSeparatorStochasticBounds (S : Alphabet) : Prop :=
  ∀ (ys : List S.Percept) (bs : List S.Action),
    ∃ e : AdmissibleDEnvironment S, e.val = scriptedSeparator ys bs ∧
      ∀ p : SPolicy S,
        (scriptReward ys : ℝ) ≤ value p (admissibleEmbedEnvironment e) ∧
        value p (admissibleEmbedEnvironment e) ≤ (scriptReward ys : ℝ) + 1

def FirstDivergenceSeparator (S : Alphabet) : Prop :=
  ∀ (p q : DPolicy S) (ys : List S.Percept), FirstDivergence p q ys →
    ∃ e : AdmissibleDEnvironment S,
      e.val = scriptedSeparator ys (scriptActions p ys) ∧
      value (embedPolicy p) (admissibleEmbedEnvironment e) = (scriptReward ys : ℝ) + 1 ∧
      value (embedPolicy q) (admissibleEmbedEnvironment e) = (scriptReward ys : ℝ)

/-- Full manuscript `lem:separator`: actual value distinction, actual admissible
deterministic environment, unrestricted integer offset, all deterministic
policies taking one of the two values, and the original policies separated. -/
def TwoValueSeparator (S : Alphabet) : Prop :=
  ∀ (p q : DPolicy S) (μ : AdmissibleSEnvironment S),
    value (embedPolicy p) μ ≠ value (embedPolicy q) μ →
      ∃ (e : AdmissibleDEnvironment S) (C : ℤ),
        (∀ r : DPolicy S, value (embedPolicy r) (admissibleEmbedEnvironment e) = (C : ℝ) ∨
          value (embedPolicy r) (admissibleEmbedEnvironment e) = (C : ℝ) + 1) ∧
        value (embedPolicy p) (admissibleEmbedEnvironment e) ≠
          value (embedPolicy q) (admissibleEmbedEnvironment e)

end LogicLineages.RL.Policy.Targets
