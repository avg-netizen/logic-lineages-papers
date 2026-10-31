module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealAutomataTargets
public import Lean.Elab.Tactic.Omega
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealAutomata.Proof
open RankedParse ProfileAutomatonEncoding

private theorem mem_step (M : Automaton) S q :
    q ∈ step M S ↔ q ∈ S ∨ ∃ x ∈ S, q ∈ M.epsilon x := by
  simp [step]

private theorem subset_step (M : Automaton) S : S ⊆ step M S := by
  intro q hq
  exact (mem_step M S q).mpr (Or.inl hq)

private theorem saturation (M : Automaton) S :
    steps M S (Fintype.card M.State + 1) = close M S := by
  have grow : ∀ n, steps M S n = steps M S (n+1) ∨ n < (steps M S (n+1)).card := by
    intro n
    induction n with
    | zero =>
        by_cases he : steps M S 0 = steps M S 1
        · exact Or.inl he
        · right
          have hlt := Finset.card_lt_card
            (Finset.ssubset_iff_subset_ne.mpr ⟨subset_step M S, he⟩)
          change S.card < (steps M S 1).card at hlt
          change 0 < (steps M S 1).card
          omega
    | succ n ih =>
        rcases ih with he | hc
        · exact Or.inl (congrArg (step M) he)
        · by_cases he : steps M S (n+1) = steps M S (n+1+1)
          · exact Or.inl he
          · right
            have hlt := Finset.card_lt_card
              (Finset.ssubset_iff_subset_ne.mpr ⟨subset_step M _, he⟩)
            change (steps M S (n+1)).card < (steps M S (n+1+1)).card at hlt
            omega
  rcases grow (Fintype.card M.State) with he | hc
  · exact he.symm
  · have hb := Finset.card_le_univ (steps M S (Fintype.card M.State+1))
    omega

private theorem seed_mem (M : Automaton) S q (h : q ∈ S) :
    q ∈ close M S := by
  have hn : ∀ n, q ∈ steps M S n := by
    intro n
    induction n with
    | zero => exact h
    | succ n ih => exact subset_step M _ ih
  exact hn _

private theorem close_edge (M : Automaton) S q r
    (h : q ∈ close M S) (he : r ∈ M.epsilon q) : r ∈ close M S := by
  rw [← saturation M S]
  exact (mem_step M _ _).mpr (Or.inr ⟨q, h, he⟩)

theorem closureExact : Targets.ClosureExact := by
  intro M S q
  constructor
  · have hn : ∀ n q, q ∈ steps M S n → Closure M S q := by
      intro n
      induction n with
      | zero => intro q h; exact .seed h
      | succ n ih =>
          intro q h
          rcases (mem_step M _ q).mp h with h | ⟨x, hx, he⟩
          · exact ih q h
          · exact .edge (ih x hx) he
    exact hn _ q
  · intro h
    induction h with
    | seed h => exact seed_mem M S _ h
    | edge _ he ih => exact close_edge M S _ _ ih he

private theorem closure_run (M : Automaton) t S
    (hs : ∀ q ∈ S, Run M t q) q (h : q ∈ close M S) : Run M t q := by
  have hc := (closureExact M S q).mp h
  clear h
  induction hc with
  | seed h => exact hs _ h
  | edge _ he ih => exact .epsilon ih he

private theorem eval_edge (M : Automaton) t q r
    (h : q ∈ evaluate M t) (he : r ∈ M.epsilon q) : r ∈ evaluate M t := by
  cases t with
  | atom => exact close_edge M _ q r h he
  | node o l u => exact close_edge M _ q r h he

private theorem mem_nodeSeeds (A : Automaton) o S T q :
    q ∈ nodeSeeds A o S T ↔ ∃ x ∈ S, ∃ y ∈ T, q ∈ A.node o x y := by
  simp [nodeSeeds]

theorem evaluationExact : Targets.EvaluationExact := by
  intro A t q
  constructor
  · induction t generalizing q with
    | atom =>
        intro h
        apply closure_run A .atom A.leaf _ q h
        intro x hx
        exact .atom hx
    | node o l r ihl ihr =>
        intro h
        apply closure_run A (.node o l r) _ _ q h
        intro z hz
        obtain ⟨x, hx, y, hy, hn⟩ := (mem_nodeSeeds A o _ _ z).mp hz
        exact .node o (ihl x hx) (ihr y hy) hn
  · intro h
    induction h with
    | atom h => exact seed_mem A _ _ h
    | node o _ _ hn ihl ihr =>
        exact seed_mem A _ _ ((mem_nodeSeeds A o _ _ _).mpr ⟨_, ihl, _, ihr, hn⟩)
    | epsilon _ he ih => exact eval_edge A _ _ _ ih he

theorem runCalibration : Targets.RunCalibration := by
  intro A t
  induction t with
  | atom => rfl
  | node o l r ihl ihr =>
      change close A (nodeSeeds A o (machineRun (determinize A) l)
        (machineRun (determinize A) r)) = _
      rw [ihl, ihr]
      rfl

theorem determinizationExact : Targets.DeterminizationExact := by
  intro A t
  rw [runCalibration A t]
  change decide (∃ q ∈ evaluate A t, q ∈ A.final) = true ↔ _
  simp only [decide_eq_true_eq, Accepts, evaluationExact A]
end LogicLineages.ModelsAlgebra.Forests.RankedIdealAutomata.Proof
