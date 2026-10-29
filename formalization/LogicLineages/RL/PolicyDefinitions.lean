module

public import Mathlib.Algebra.Order.Ring.Rat
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

/-! Paper 13 actual policy domains. Only probability-distribution constructor
invariants are proved here; semantic theorems belong in separate proof files. -/
@[expose] public section

namespace LogicLineages.RL.Policy

/-- Finite nonempty alphabets; no assumption that there are two actions.
Tagged letters below enforce disjointness even if the carrier types coincide. -/
structure Alphabet where
  Action : Type
  Percept : Type
  actionFintype : Fintype Action
  perceptFintype : Fintype Percept
  actionNonempty : Nonempty Action
  perceptNonempty : Nonempty Percept
  reward : Percept → ℤ
  zeroPercept : Percept
  onePercept : Percept
  reward_zero : reward zeroPercept = 0
  reward_one : reward onePercept = 1

attribute [instance] Alphabet.actionFintype Alphabet.perceptFintype
  Alphabet.actionNonempty Alphabet.perceptNonempty

/-- A rational probability distribution, not an arbitrary real-valued score. -/
structure Kernel (X : Type) [Fintype X] where
  mass : X → ℚ
  nonneg : ∀ x, 0 ≤ mass x
  sum_one : ∑ x, mass x = 1

abbrev RatUnit := {t : ℚ // 0 ≤ t ∧ t ≤ 1}

def zeroWeight : RatUnit := ⟨0, by constructor <;> decide⟩
def oneWeight : RatUnit := ⟨1, by constructor <;> decide⟩

noncomputable def dirac {X : Type} [Fintype X] (x : X) : Kernel X := by
  classical
  exact ⟨fun y => if y = x then 1 else 0,
    fun y => by split <;> norm_num,
    by simp⟩

/-- Ordinary convex combination of distributions; not the general behavioral
mixture of whole policies in the later source lemma. -/
def kernelMix {X : Type} [Fintype X] (t : RatUnit)
    (k l : Kernel X) : Kernel X where
  mass x := (1 - t.val) * k.mass x + t.val * l.mass x
  nonneg x := add_nonneg
    (mul_nonneg (sub_nonneg.mpr t.property.2) (k.nonneg x))
    (mul_nonneg t.property.1 (l.nonneg x))
  sum_one := by
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, k.sum_one, l.sum_one]
    ring

abbrev Letter (S : Alphabet) := S.Action ⊕ S.Percept
abbrev EnvHistory (S : Alphabet) := List (S.Percept × S.Action)
abbrev AgentHistory (S : Alphabet) := EnvHistory S × S.Percept

abbrev DPolicy (S : Alphabet) := AgentHistory S → S.Action
abbrev SPolicy (S : Alphabet) := AgentHistory S → Kernel S.Action
abbrev DEnvironment (S : Alphabet) := EnvHistory S → S.Percept
abbrev SEnvironment (S : Alphabet) := EnvHistory S → Kernel S.Percept

noncomputable def embedPolicy {S : Alphabet} (p : DPolicy S) : SPolicy S :=
  fun h => dirac (p h)
noncomputable def embedEnvironment {S : Alphabet} (μ : DEnvironment S) : SEnvironment S :=
  fun h => dirac (μ h)

def constantPolicy {S : Alphabet} (a : S.Action) : DPolicy S := fun _ => a

def firstThenPolicy {S : Alphabet} (a₀ a₁ : S.Action) : DPolicy S :=
  fun h => if h.1.isEmpty then a₁ else a₀

/-- Only the first action varies, independently of the initial percept.
All later and all off-path histories have the same fixed continuation. -/
noncomputable def firstActionMixture {S : Alphabet}
    (a₀ a₁ : S.Action) (t : RatUnit) : SPolicy S :=
  fun h => if h.1.isEmpty then kernelMix t (dirac a₀) (dirac a₁) else dirac a₀

def encodeEnv {S : Alphabet} : EnvHistory S → List (Letter S)
  | [] => []
  | (z, a) :: h => Sum.inr z :: Sum.inl a :: encodeEnv h

def encodeAgent {S : Alphabet} (h : AgentHistory S) : List (Letter S) :=
  encodeEnv h.1 ++ [Sum.inr h.2]

/-- Independent literal alternating-word grammars. -/
inductive IsEnvWord (S : Alphabet) : List (Letter S) → Prop
  | nil : IsEnvWord S []
  | pair (z : S.Percept) (a : S.Action) {w : List (Letter S)} :
      IsEnvWord S w → IsEnvWord S (Sum.inr z :: Sum.inl a :: w)

inductive IsAgentWord (S : Alphabet) : List (Letter S) → Prop
  | last (z : S.Percept) : IsAgentWord S [Sum.inr z]
  | pair (z : S.Percept) (a : S.Action) {w : List (Letter S)} :
      IsAgentWord S w → IsAgentWord S (Sum.inr z :: Sum.inl a :: w)

def perceptCount {S : Alphabet} (w : List (Letter S)) : ℕ :=
  (w.filter fun x => match x with | Sum.inl _ => false | Sum.inr _ => true).length

def actionCount {S : Alphabet} (w : List (Letter S)) : ℕ :=
  (w.filter fun x => match x with | Sum.inl _ => true | Sum.inr _ => false).length

end LogicLineages.RL.Policy
