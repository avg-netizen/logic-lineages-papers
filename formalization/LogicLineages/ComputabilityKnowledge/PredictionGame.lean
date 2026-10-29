module

public import Init

@[expose] public section

/-!
# The actual finite-history adversarial prediction game

Paper 14 has simultaneous moves: the predictor receives previous evasions,
and the evader receives previous predictions. Neither sees the other player's
current move. This module fixes that semantics and proves the semantic
anti-predictor construction. It does not yet supply ordinary program indices,
computability, worst-case runtimes, hierarchy or measure conclusions.
-/

namespace LogicLineages.ComputabilityKnowledge.PredictionGame

abbrev Policy := List Bool → Bool

structure Histories where
  evasions : List Bool
  predictions : List Bool

def advance (predictor evader : Policy) (h : Histories) : Histories where
  evasions := h.evasions ++ [evader h.predictions]
  predictions := h.predictions ++ [predictor h.evasions]

def histories (predictor evader : Policy) : Nat → Histories
  | 0 => ⟨[], []⟩
  | n + 1 => advance predictor evader (histories predictor evader n)

def prediction (predictor evader : Policy) (n : Nat) : Bool :=
  predictor (histories predictor evader n).evasions

def evasion (predictor evader : Policy) (n : Nat) : Bool :=
  evader (histories predictor evader n).predictions

def Learns (predictor evader : Policy) : Prop :=
  ∃ cutoff : Nat, ∀ n : Nat, cutoff ≤ n → prediction predictor evader n = evasion predictor evader n

theorem history_lengths (predictor evader : Policy) (n : Nat) :
    (histories predictor evader n).evasions.length = n ∧
      (histories predictor evader n).predictions.length = n := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
      simpa only [histories, advance, List.length_append, List.length_cons,
        List.length_nil, ih.1, ih.2] using
        (And.intro (rfl : n + 1 = n + 1) (rfl : n + 1 = n + 1))

theorem evasion_prefix (predictor evader : Policy) (n : Nat) :
    (histories predictor evader (n + 1)).evasions =
      (histories predictor evader n).evasions ++ [evasion predictor evader n] := rfl

theorem prediction_prefix (predictor evader : Policy) (n : Nat) :
    (histories predictor evader (n + 1)).predictions =
      (histories predictor evader n).predictions ++ [prediction predictor evader n] := rfl

def antiPrefix (predictor : Policy) : Nat → List Bool
  | 0 => []
  | n + 1 => antiPrefix predictor n ++ [!(predictor (antiPrefix predictor n))]

def antiEvader (predictor : Policy) : Policy :=
  fun history => !(predictor (antiPrefix predictor history.length))

theorem anti_history (predictor : Policy) (n : Nat) :
    (histories predictor (antiEvader predictor) n).evasions = antiPrefix predictor n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [evasion_prefix]
      change (histories predictor (antiEvader predictor) n).evasions ++
        [!(predictor (antiPrefix predictor
          (histories predictor (antiEvader predictor) n).predictions.length))] =
        antiPrefix predictor (n + 1)
      rw [(history_lengths predictor (antiEvader predictor) n).2, ih]
      rfl

private theorem bool_ne_not_self (b : Bool) : b ≠ !b := by
  cases b <;> decide

theorem anti_disagrees (predictor : Policy) (n : Nat) :
    prediction predictor (antiEvader predictor) n ≠
      evasion predictor (antiEvader predictor) n := by
  change predictor (histories predictor (antiEvader predictor) n).evasions ≠
    !(predictor (antiPrefix predictor
      (histories predictor (antiEvader predictor) n).predictions.length))
  rw [(history_lengths predictor (antiEvader predictor) n).2,
    anti_history predictor n]
  exact bool_ne_not_self _

theorem anti_not_learned (predictor : Policy) : ¬ Learns predictor (antiEvader predictor) := by
  rintro ⟨cutoff, h⟩
  exact anti_disagrees predictor cutoff (h cutoff (Nat.le_refl cutoff))

end LogicLineages.ComputabilityKnowledge.PredictionGame
