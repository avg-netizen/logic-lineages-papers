module

public import LogicLineages.RL.InteractionDefinitions

/-! Literal finite-script objects for paper 13 `lem:separator`.
Scripts retain arbitrary signed integer percept rewards and continue after
unexpected actions. Value distinction, admissibility and separation are not
assumed by these definitions; they are separate exact targets. -/
@[expose] public section

namespace LogicLineages.RL.Policy

def scriptHistoryFrom {S : Alphabet} (p : DPolicy S) :
    EnvHistory S → List S.Percept → EnvHistory S
  | h, [] => h
  | h, z :: ys => scriptHistoryFrom p (h ++ [(z, p (h, z))]) ys

def scriptHistory {S : Alphabet} (p : DPolicy S) (ys : List S.Percept) : EnvHistory S :=
  scriptHistoryFrom p [] ys

def scriptActions {S : Alphabet} (p : DPolicy S) (ys : List S.Percept) : List S.Action :=
  (scriptHistory p ys).map Prod.snd

def scriptReward {S : Alphabet} (ys : List S.Percept) : ℤ := (ys.map S.reward).sum

/-- The first differing response occurs after an identical earlier scripted
history, not merely at an arbitrary syntactically different off-path input. -/
def FirstDivergence {S : Alphabet} (p q : DPolicy S) (ys : List S.Percept) : Prop :=
  ∃ prior z, ys = prior ++ [z] ∧
    scriptHistory p prior = scriptHistory q prior ∧
    p (scriptHistory p prior, z) ≠ q (scriptHistory q prior, z)

/-- Emit the entire script independently of actions; then one indicator
reward for an exact recorded action sequence; then zero forever. -/
noncomputable def scriptedSeparator {S : Alphabet} (ys : List S.Percept)
    (bs : List S.Action) : DEnvironment S := by
  classical
  exact fun h => if hl : h.length < ys.length then ys.get ⟨h.length, hl⟩
    else if h.length = ys.length ∧ h.map Prod.snd = bs then S.onePercept
    else S.zeroPercept

/-- Literal zero reward after a finite history depth, with no constraint on
earlier rewards, histories, or the policy class. -/
def RewardZeroAfter {S : Alphabet} (μ : DEnvironment S) (N : ℕ) : Prop :=
  ∀ h : EnvHistory S, N ≤ h.length → S.reward (μ h) = 0

end LogicLineages.RL.Policy
