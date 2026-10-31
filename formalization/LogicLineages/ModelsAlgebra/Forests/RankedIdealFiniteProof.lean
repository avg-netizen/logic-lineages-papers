module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealFiniteTargets
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealCompletionStatementChecks
public import Lean.Elab.Tactic.Omega
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealFinite.Proof
open RankedParse ProfileAutomatonEncoding ProfileLanguageEmpty RankedIdealCompletion

theorem successorsExact : Targets.SuccessorsExact := by
  intro M _ x y
  have ho : ∀ o : Operation, o ∈ operations := by intro o; cases o <;> simp [operations]
  simp only [successors, Epsilon]
  split_ifs with hx
  · simp [hx, ho]
  · simp [hx]

private theorem mem_step (M : Machine) [DecidableEq M.State] S q :
    q ∈ step M S ↔ q ∈ S ∨ ∃ x ∈ S, Epsilon M x q := by
  simp [step, successorsExact M]

private theorem subset_step (M : Machine) [DecidableEq M.State] S : S ⊆ step M S := by
  intro q hq
  exact (mem_step M S q).mpr (Or.inl hq)

private theorem saturation (M : Machine) [DecidableEq M.State] S :
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

private theorem seed_mem (M : Machine) [DecidableEq M.State] S q (h : q ∈ S) :
    q ∈ close M S := by
  have hn : ∀ n, q ∈ steps M S n := by
    intro n
    induction n with
    | zero => exact h
    | succ n ih => exact subset_step M _ ih
  exact hn _

private theorem close_edge (M : Machine) [DecidableEq M.State] S q r
    (h : q ∈ close M S) (he : Epsilon M q r) : r ∈ close M S := by
  rw [← saturation M S]
  exact (mem_step M _ _).mpr (Or.inr ⟨q, h, he⟩)

theorem closureExact : Targets.ClosureExact := by
  intro M _ S q
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

private theorem closure_run (M : Machine) [DecidableEq M.State] t S
    (hs : ∀ q ∈ S, Run M t q) q (h : q ∈ close M S) : Run M t q := by
  have hc := (closureExact M S q).mp h
  clear h
  induction hc with
  | seed h => exact hs _ h
  | edge _ he ih => exact .epsilon ih he

private theorem eval_edge (M : Machine) [DecidableEq M.State] t q r
    (h : q ∈ evaluate M t) (he : Epsilon M q r) : r ∈ evaluate M t := by
  cases t with
  | atom => exact close_edge M _ q r h he
  | node o l u => exact close_edge M _ q r h he

private theorem mem_nodeSeeds (M : Machine) [DecidableEq M.State] o S T q :
    q ∈ nodeSeeds M o S T ↔ ∃ x ∈ S, x ∈ productive M ∧
      ∃ y ∈ T, y ∈ productive M ∧ M.node o x y = q := by
  simp [nodeSeeds, and_assoc, exists_and_left, exists_and_right]

theorem evaluationExact : Targets.EvaluationExact := by
  intro M _ t q
  constructor
  · induction t generalizing q with
    | atom =>
        intro h
        apply closure_run M .atom {M.leaf} _ q h
        intro x hx
        have he : x = M.leaf := Finset.mem_singleton.mp hx
        subst x
        exact .atom
    | node o l r ihl ihr =>
        intro h
        apply closure_run M (.node o l r) _ _ q h
        intro z hz
        obtain ⟨x, hx, hpx, y, hy, hpy, rfl⟩ := (mem_nodeSeeds M o _ _ z).mp hz
        exact .node o (ihl x hx) (ihr y hy) hpx hpy
  · intro h
    induction h with
    | atom => exact seed_mem M _ _ (Finset.mem_singleton_self _)
    | node o _ _ hx hy ihl ihr =>
        exact seed_mem M _ _ ((mem_nodeSeeds M o _ _ _).mpr
          ⟨_, ihl, hx, _, ihr, hy, rfl⟩)
    | epsilon _ he ih => exact eval_edge M _ _ _ ih he

theorem acceptanceExact : Targets.AcceptanceExact := by
  intro M _ t
  rw [← RankedIdealCompletion.StatementChecks.acceptanceExact M t]
  simp only [accepts, decide_eq_true_eq, RankedIdealCompletion.Accepts, evaluationExact M]
end LogicLineages.ModelsAlgebra.Forests.RankedIdealFinite.Proof
