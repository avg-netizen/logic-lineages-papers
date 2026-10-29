module

public import LogicLineages.RL.Definitions
public import LogicLineages.RL.PolicyDefinitions
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Data.Fintype.Sum

/-! Concrete percept-first trace laws and limiting reward values. No semantic
correctness theorem, affine law or arbitrary value oracle is a structure field. -/
@[expose] public section

namespace LogicLineages.RL.Policy

/-- `PositiveTrace S n` records n completed percept/action pairs followed by
one terminal percept: n+1 rewards and no extra final action. -/
def PositiveTrace (S : Alphabet) : ℕ → Type
  | 0 => S.Percept
  | n + 1 => S.Percept × S.Action × PositiveTrace S n

instance positiveTraceFintype (S : Alphabet) : (n : ℕ) → Fintype (PositiveTrace S n)
  | 0 => S.perceptFintype
  | n + 1 => by
      letI := positiveTraceFintype S n
      exact inferInstanceAs (Fintype (S.Percept × S.Action × PositiveTrace S n))

/-- Horizon zero is the empty trace; horizon n+1 is a positive trace. -/
def Trace (S : Alphabet) : ℕ → Type
  | 0 => Unit
  | n + 1 => PositiveTrace S n

instance traceFintype (S : Alphabet) : (n : ℕ) → Fintype (Trace S n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n + 1 => positiveTraceFintype S n

def positiveTraceWord {S : Alphabet} : (n : ℕ) → PositiveTrace S n → List (Letter S)
  | 0, z => [Sum.inr z]
  | n + 1, (z, a, rest) => Sum.inr z :: Sum.inl a :: positiveTraceWord n rest

def traceWord {S : Alphabet} : (n : ℕ) → Trace S n → List (Letter S)
  | 0, _ => []
  | n + 1, tr => positiveTraceWord n tr

/-- Actual alternating kernel product, evaluated on a fixed trace. -/
def positiveWeight {S : Alphabet} (p : SPolicy S) (μ : SEnvironment S) :
    (n : ℕ) → EnvHistory S → PositiveTrace S n → ℚ
  | 0, h, z => (μ h).mass z
  | n + 1, h, (z, a, rest) =>
      (μ h).mass z * (p (h, z)).mass a *
        positiveWeight p μ n (h ++ [(z, a)]) rest

def traceWeight {S : Alphabet} (p : SPolicy S) (μ : SEnvironment S) :
    (n : ℕ) → Trace S n → ℚ
  | 0, _ => 1
  | n + 1, tr => positiveWeight p μ n [] tr

def positiveReward {S : Alphabet} : (n : ℕ) → PositiveTrace S n → ℤ
  | 0, z => S.reward z
  | n + 1, (z, _, rest) => S.reward z + positiveReward n rest

def traceReward {S : Alphabet} : (n : ℕ) → Trace S n → ℤ
  | 0, _ => 0
  | n + 1, tr => positiveReward n tr

/-- Sum of precisely the first n percept rewards, including the initial one. -/
noncomputable def finiteValue {S : Alphabet} (p : SPolicy S)
    (μ : SEnvironment S) (n : ℕ) : ℝ :=
  ∑ tr : Trace S n, (traceWeight p μ n tr : ℝ) * (traceReward n tr : ℝ)

/-- Literal-word probability evaluator, separately parsing the alternating
process. Malformed words have weight zero. The empty word has weight one. -/
def literalWeight {S : Alphabet} (p : SPolicy S) (μ : SEnvironment S) :
    EnvHistory S → List (Letter S) → ℚ
  | _, [] => 1
  | h, [Sum.inr z] => (μ h).mass z
  | h, Sum.inr z :: Sum.inl a :: rest =>
      (μ h).mass z * (p (h, z)).mass a *
        literalWeight p μ (h ++ [(z, a)]) rest
  | _, _ => 0

def literalReward {S : Alphabet} (w : List (Letter S)) : ℤ :=
  (w.map fun x => match x with | Sum.inl _ => 0 | Sum.inr z => S.reward z).sum

/-- Deterministic play, generated recursively from the actual history. -/
def deterministicTrace {S : Alphabet} (p : DPolicy S) (μ : DEnvironment S) :
    (n : ℕ) → EnvHistory S → PositiveTrace S n
  | 0, h => μ h
  | n + 1, h =>
      let z := μ h
      let a := p (h, z)
      (z, a, deterministicTrace p μ n (h ++ [(z, a)]))

open Filter Topology

/-- Full source admissibility: every policy of either kind, with no common
bound on the resulting real values. The first conjunct is intentionally
explicit even though deterministic policies embed among stochastic ones. -/
def Admissible {S : Alphabet} (μ : SEnvironment S) : Prop :=
  (∀ p : DPolicy S, ∃ v : ℝ,
    Tendsto (finiteValue (embedPolicy p) μ) atTop (𝓝 v)) ∧
  (∀ p : SPolicy S, ∃ v : ℝ,
    Tendsto (finiteValue p μ) atTop (𝓝 v))

abbrev AdmissibleDEnvironment (S : Alphabet) :=
  {μ : DEnvironment S // Admissible (embedEnvironment μ)}
abbrev AdmissibleSEnvironment (S : Alphabet) :=
  {μ : SEnvironment S // Admissible μ}

/-- The value is selected from the actual limiting-expectation proposition.
Its convergence and uniqueness are independent semantic targets. -/
noncomputable def value {S : Alphabet} (p : SPolicy S)
    (μ : AdmissibleSEnvironment S) : ℝ :=
  Classical.choose (μ.property.2 p)

noncomputable def admissibleEmbedEnvironment {S : Alphabet}
    (μ : AdmissibleDEnvironment S) : AdmissibleSEnvironment S :=
  ⟨embedEnvironment μ.val, μ.property⟩

inductive Kind where
  | deterministic
  | stochastic
  deriving DecidableEq

def Agent (S : Alphabet) : Kind → Type
  | .deterministic => DPolicy S
  | .stochastic => SPolicy S

def Environment (S : Alphabet) : Kind → Type
  | .deterministic => AdmissibleDEnvironment S
  | .stochastic => AdmissibleSEnvironment S

noncomputable def agentKernel {S : Alphabet} : (k : Kind) → Agent S k → SPolicy S
  | .deterministic, p => embedPolicy p
  | .stochastic, p => p

noncomputable def environmentKernel {S : Alphabet} :
    (k : Kind) → Environment S k → AdmissibleSEnvironment S
  | .deterministic, μ => admissibleEmbedEnvironment μ
  | .stochastic, μ => μ

/-- The four frameworks of Definition `def:four`, with actual policy spaces
and actual derived limit values; singleton action alphabets remain allowed. -/
noncomputable def framework (S : Alphabet) (agents environments : Kind) :
    LogicLineages.RL.Framework where
  Agent := Agent S agents
  Environment := Environment S environments
  value p μ := value (agentKernel agents p) (environmentKernel environments μ)

end LogicLineages.RL.Policy
