module
public import LogicLineages.ModelsAlgebra.Forests.ProfileLanguageEmptyTargets
public import LogicLineages.ModelsAlgebra.Forests.ProfileSourceRegularProof
public import Lean.Elab.Tactic.Omega
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.ProfileLanguageEmpty.Proof
open RankedParse ProfileAutomatonEncoding ProfileSourceRegular ForestParseRepresentation

private theorem height_pos (t : Term) : 0 < termHeight t := by
  cases t <;> simp [termHeight] <;> omega

@[simp] private theorem mem_operations (o : Operation) : o ∈ operations := by
  cases o <;> simp [operations]

private theorem mem_step (M : Machine) [DecidableEq M.State]
    (S : Finset M.State) (s : M.State) :
    s ∈ reachStep M S ↔ s ∈ S ∨ s = M.leaf ∨
      ∃ o x, x ∈ S ∧ ∃ y, y ∈ S ∧ M.node o x y = s := by
  simp [reachStep, or_assoc, or_left_comm]

private theorem subset_step (M : Machine) [DecidableEq M.State] (S : Finset M.State) :
    S ⊆ reachStep M S := by
  intro s hs
  exact (mem_step M S s).mpr (Or.inl hs)

theorem reachableHeightExact : Targets.ReachableHeightExact := by
  intro M _ n
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
      · rintro (hs | hs | ⟨o, x, hx, y, hy, hxy⟩)
        · obtain ⟨t, ht, hrun⟩ := (ih s).mp hs
          exact ⟨t, by omega, hrun⟩
        · exact ⟨.atom, by simp [termHeight], hs.symm⟩
        · obtain ⟨l, hl, hrl⟩ := (ih x).mp hx
          obtain ⟨r, hr, hrr⟩ := (ih y).mp hy
          refine ⟨.node o l r, ?_, ?_⟩
          · simp only [termHeight]
            omega
          · simpa only [machineRun, hrl, hrr] using hxy
      · rintro ⟨t, ht, hrun⟩
        cases t with
        | atom => exact Or.inr (Or.inl hrun.symm)
        | node o l r =>
            have hl : termHeight l ≤ n := by simp only [termHeight] at ht; omega
            have hr : termHeight r ≤ n := by simp only [termHeight] at ht; omega
            exact Or.inr (Or.inr ⟨o, machineRun M l, (ih _).mpr ⟨l, hl, rfl⟩,
              machineRun M r, (ih _).mpr ⟨r, hr, rfl⟩, hrun⟩)

theorem reachableSaturation : Targets.ReachableSaturation := by
  intro M _
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
  rcases grow (Fintype.card M.State) with he | hc
  · exact he.symm
  · have hb : (reachable M (Fintype.card M.State + 1)).card ≤ Fintype.card M.State :=
      Finset.card_le_univ _
    omega

theorem allRunsReachable (M : Machine) [DecidableEq M.State] (t : Term) :
    machineRun M t ∈ reachable M (Fintype.card M.State) := by
  have hs := reachableSaturation M
  induction t with
  | atom =>
      rw [← hs]
      exact (mem_step M _ _).mpr (Or.inr (Or.inl rfl))
  | node o l r ihl ihr =>
      rw [← hs]
      exact (mem_step M _ _).mpr
        (Or.inr (Or.inr ⟨o, machineRun M l, ihl, machineRun M r, ihr, rfl⟩))

theorem machineEmptyCorrect : Targets.MachineEmptyCorrect := by
  intro M _
  simp only [languageEmpty, decide_eq_true_eq]
  constructor
  · intro hnone
    rintro ⟨t, ht⟩
    have ha : machineRun M t ∈ acceptingStates M := by simp [acceptingStates, ht]
    have hm := Finset.mem_inter.mpr ⟨allRunsReachable M t, ha⟩
    rw [hnone] at hm
    exact Finset.notMem_empty _ hm
  · intro hnone
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro s hs
    obtain ⟨hr, ha⟩ := Finset.mem_inter.mp hs
    obtain ⟨t, _, hrun⟩ := (reachableHeightExact M (Fintype.card M.State) s).mp hr
    have hacc : M.accept s = true := by simpa [acceptingStates] using ha
    exact hnone ⟨t, by simpa only [hrun] using hacc⟩

theorem sourceEmptyCorrect : Targets.SourceEmptyCorrect := by
  intro F
  unfold sourceLanguageEmpty
  rw [machineEmptyCorrect]
  constructor
  · intro hnone
    rintro ⟨t, ht⟩
    exact hnone ⟨t, (ProfileSourceRegular.Proof.sourceMachineCorrect F t).mpr ht⟩
  · intro hnone
    rintro ⟨t, ht⟩
    exact hnone ⟨t, (ProfileSourceRegular.Proof.sourceMachineCorrect F t).mp ht⟩

end LogicLineages.ModelsAlgebra.Forests.ProfileLanguageEmpty.Proof
