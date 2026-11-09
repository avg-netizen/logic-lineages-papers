module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockSplitOccurrenceProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockSplitProof
open BlockRows PlainBlockSplit

theorem branch_allowed (bound : List Nat) (p : Formula) (s : State)
    (hallowed : TiedLinear.allowed bound p = true) (hparams : ParametersIndependent bound p)
    (hs : s ∈ branches bound p) : TiedLinear.allowed s.1 s.2 = true := by
  change s ∈ ((small bound p ++ ties bound p) ++ bands bound p) ++ far bound p at hs
  rcases List.mem_append.mp hs with hleft | hfar
  · rcases List.mem_append.mp hleft with hleft | hbands
    · rcases List.mem_append.mp hleft with hsmall | hties
      · cases bound with
        | nil => simp [small] at hsmall
        | cons i rest =>
          obtain ⟨n, _, rfl⟩ := List.mem_map.mp hsmall
          exact allowed_substitute (i :: rest) p i (.numeral n) hallowed
      · obtain ⟨i, _, hinner⟩ := List.mem_flatMap.mp hties
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hinner
        obtain ⟨hj, hji⟩ := List.mem_filter.mp hj
        exact allowed_rename bound p i j hallowed hj (by simpa using hji)
    · obtain ⟨i, _, hinner⟩ := List.mem_flatMap.mp hbands
      obtain ⟨a, _, ha⟩ := List.mem_flatMap.mp hinner
      cases a with
      | nonnegative r =>
        change s ∈ (if PlainMaximum.headCoefficient i r = 0 then [] else
          (List.range 5).map (fun d => (bound.erase i, p.substitute i (bandCandidate i r d)))) at ha
        by_cases hz : PlainMaximum.headCoefficient i r = 0
        · simp only [if_pos hz, List.not_mem_nil] at ha
        · rw [if_neg hz] at ha
          obtain ⟨d, _, rfl⟩ := List.mem_map.mp ha
          exact allowed_substitute bound p i (bandCandidate i r d) hallowed
      | divisible m r => exact False.elim (List.not_mem_nil ha)
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hfar
    exact far_allowed bound p i hi hallowed hparams

theorem branch_bound_subset (bound : List Nat) (p : Formula) (s : State)
    (hs : s ∈ branches bound p) (j : Nat) (hj : j ∈ s.1) : j ∈ bound := by
  obtain ⟨i, _, he⟩ := branches_erase_bound bound p s hs
  rw [he] at hj
  exact List.mem_of_mem_erase hj

theorem wholeBlockStateClosure : PlainBlockSplitTargets.WholeBlockStateClosure := by
  intro bound p hallowed hparams s hs
  refine ⟨branch_allowed bound p s hallowed hparams hs, ?_⟩
  intro j hj hnew
  exact hparams j (branch_bound_subset bound p s hs j hj) (branch_parameter_support bound p s hs j hnew)

theorem parameters_in_variables (p : Formula) (j : Nat) (hj : j ∈ p.parameters) : j ∈ p.variables := by
  induction p with
  | truth => simp [Formula.parameters] at hj
  | falsity => simp [Formula.parameters] at hj
  | atom a => exact List.mem_append_left _ hj
  | negative p ih => exact ih hj
  | conjunction p q ihp ihq =>
    rcases List.mem_append.mp hj with h | h
    · exact List.mem_append_left _ (ihp h)
    · exact List.mem_append_right _ (ihq h)
  | disjunction p q ihp ihq =>
    rcases List.mem_append.mp hj with h | h
    · exact List.mem_append_left _ (ihp h)
    · exact List.mem_append_right _ (ihq h)

theorem variable_cases (p : Formula) (j : Nat) (hj : j ∈ p.variables) :
    j ∈ p.parameters ∨ ∃ a ∈ PlainMaximum.occurrences p, j = a.2.name := by
  induction p with
  | truth => simp [Formula.variables] at hj
  | falsity => simp [Formula.variables] at hj
  | atom a =>
    rcases List.mem_append.mp hj with hparam | ho
    · exact Or.inl hparam
    · obtain ⟨b, hb, he⟩ := List.mem_map.mp ho
      exact Or.inr ⟨b, hb, he.symm⟩
  | negative p ih => exact ih hj
  | conjunction p q ihp ihq =>
    rcases List.mem_append.mp hj with hp | hq
    · rcases ihp hp with hparam | ⟨a, ha, he⟩
      · exact Or.inl (List.mem_append_left _ hparam)
      · exact Or.inr ⟨a, List.mem_append_left _ ha, he⟩
    · rcases ihq hq with hparam | ⟨a, ha, he⟩
      · exact Or.inl (List.mem_append_right _ hparam)
      · exact Or.inr ⟨a, List.mem_append_right _ ha, he⟩
  | disjunction p q ihp ihq =>
    rcases List.mem_append.mp hj with hp | hq
    · rcases ihp hp with hparam | ⟨a, ha, he⟩
      · exact Or.inl (List.mem_append_left _ hparam)
      · exact Or.inr ⟨a, List.mem_append_left _ ha, he⟩
    · rcases ihq hq with hparam | ⟨a, ha, he⟩
      · exact Or.inl (List.mem_append_right _ hparam)
      · exact Or.inr ⟨a, List.mem_append_right _ ha, he⟩

theorem allowed_summand_name (bound : List Nat) (s : NormalForm.Summand)
    (hs : PlainMaximum.allowedSummand bound s = true) : s.name ∈ bound := by
  cases s with
  | «variable» j => simpa [PlainMaximum.allowedSummand] using hs
  | phi j shift =>
    have h : j ∈ bound ∧ shift = 0 := by simpa [PlainMaximum.allowedSummand] using hs
    exact h.1
  | hyperPhi j e h => simp [PlainMaximum.allowedSummand] at hs

theorem originalBranchNameSupport : PlainBlockSplitTargets.OriginalBranchNameSupport := by
  intro bound p hallowed hparams s hs j hj
  rcases variable_cases s.2 j hj with hparam | ⟨a, ha, he⟩
  · exact Or.inl (parameters_in_variables p j (branch_parameter_support bound p s hs j hparam))
  · have hclass := (TiedLinearProof.allowed_formula_iff s.1 s.2).mp
      (branch_allowed bound p s hallowed hparams hs) a ha
    have hmem : j ∈ s.1 := by
      rw [he]
      exact allowed_summand_name s.1 a.2 hclass
    exact Or.inr (branch_bound_subset bound p s hs j hmem)

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockSplitProof
