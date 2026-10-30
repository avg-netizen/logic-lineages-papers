module

public import LogicLineages.ModelsAlgebra.Forests.CarterAutomataTargets
public import Mathlib.Data.Fintype.Card
public import Lean.Elab.Tactic.Omega

/-! Finite saturation proves exact tree-language emptiness; no unbounded
bad-pair search or graph/tree embedding supplier is assumed. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.CarterAutomataProof

open CarterAutomata

private theorem height_pos {k} (t : BinaryLabelTree k) : 0 < height t := by
  cases t <;> simp [height] <;> omega

private theorem mem_step {k q} (M : Automaton k q) (S : Finset (Fin q)) (s : Fin q) :
    s ∈ reachStep M S ↔ s ∈ S ∨ (∃ a, M.leafState a = s) ∨
      ∃ a x, x ∈ S ∧ ∃ y, y ∈ S ∧ M.nodeState a x y = s := by
  simp [reachStep, or_assoc]

private theorem subset_step {k q} (M : Automaton k q) (S : Finset (Fin q)) :
    S ⊆ reachStep M S := by
  intro s hs
  exact (mem_step M S s).mpr (Or.inl hs)

theorem carterReachableHeightExact : Targets.CarterReachableHeightExact := by
  intro k q M n
  induction n with
  | zero =>
      intro s
      constructor
      · simp [reachable]
      · rintro ⟨t, ht, _⟩
        have := height_pos t
        omega
  | succ n ih =>
      intro s
      change s ∈ reachStep M (reachable M n) ↔ _
      rw [mem_step]
      constructor
      · rintro (hs | ⟨a, ha⟩ | ⟨a, x, hx, y, hy, hxy⟩)
        · obtain ⟨t, ht, hrun⟩ := (ih s).mp hs
          exact ⟨t, by omega, hrun⟩
        · exact ⟨.leaf a, by simp [height], ha⟩
        · obtain ⟨l, hl, hrl⟩ := (ih x).mp hx
          obtain ⟨r, hr, hrr⟩ := (ih y).mp hy
          refine ⟨.node a l r, ?_, ?_⟩
          · simp only [height]
            omega
          · simpa only [run, hrl, hrr] using hxy
      · rintro ⟨t, ht, hrun⟩
        cases t with
        | leaf a => exact Or.inr (Or.inl ⟨a, hrun⟩)
        | node a l r =>
            have hl : height l ≤ n := by simp only [height] at ht; omega
            have hr : height r ≤ n := by simp only [height] at ht; omega
            exact Or.inr (Or.inr ⟨a, run M l, (ih _).mpr ⟨l, hl, rfl⟩,
              run M r, (ih _).mpr ⟨r, hr, rfl⟩, hrun⟩)

theorem carterReachableSaturation : Targets.CarterReachableSaturation := by
  intro k q M
  have grow : ∀ n, reachable M n = reachable M (n + 1) ∨
      n < (reachable M (n + 1)).card := by
    intro n
    induction n with
    | zero =>
        by_cases he : reachable M 0 = reachable M 1
        · exact Or.inl he
        · right
          apply Finset.card_pos.mpr
          apply Finset.nonempty_iff_ne_empty.mpr
          intro h
          exact he h.symm
    | succ n ih =>
        rcases ih with he | hc
        · exact Or.inl (congrArg (reachStep M) he)
        · by_cases he : reachable M (n + 1) = reachable M (n + 1 + 1)
          · exact Or.inl he
          · right
            have hlt := Finset.card_lt_card
              (Finset.ssubset_iff_subset_ne.mpr ⟨subset_step M _, he⟩)
            change (reachable M (n + 1)).card < (reachable M (n + 1 + 1)).card at hlt
            omega
  rcases grow q with he | hc
  · exact he.symm
  · have hb : (reachable M (q + 1)).card ≤ q := by
      simpa using Finset.card_le_univ (reachable M (q + 1))
    omega

theorem carterAllRunsReachable : Targets.CarterAllRunsReachable := by
  intro k q M t
  have hs := carterReachableSaturation k q M
  induction t with
  | leaf a =>
      rw [← hs]
      exact (mem_step M _ _).mpr (Or.inr (Or.inl ⟨a, rfl⟩))
  | node a l r ihl ihr =>
      rw [← hs]
      exact (mem_step M _ _).mpr
        (Or.inr (Or.inr ⟨a, run M l, ihl, run M r, ihr, rfl⟩))

theorem carterLanguageEmptiness : Targets.CarterLanguageEmptiness := by
  intro k q M
  simp only [languageEmpty, decide_eq_true_eq]
  constructor
  · intro hnone
    rintro ⟨t, ht⟩
    have hm := Finset.mem_inter.mpr ⟨carterAllRunsReachable k q M t, ht⟩
    rw [hnone] at hm
    exact Finset.notMem_empty _ hm
  · intro hnone
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro s hs
    obtain ⟨hr, ha⟩ := Finset.mem_inter.mp hs
    obtain ⟨t, _, hrun⟩ := (carterReachableHeightExact k q M q s).mp hr
    exact hnone ⟨t, by simpa only [accepts, hrun] using ha⟩

theorem carterUnorderedRunInvariant : Targets.CarterUnorderedRunInvariant := by
  intro k q M hsym s t h
  induction h with
  | leaf a => rfl
  | node h₁ h₂ ih₁ ih₂ => simp only [run, ih₁, ih₂]
  | @swap a l r l' r' h₁ h₂ ih₁ ih₂ =>
      simp only [run, ih₁, ih₂]
      exact hsym a _ _

end LogicLineages.ModelsAlgebra.Forests.CarterAutomataProof
