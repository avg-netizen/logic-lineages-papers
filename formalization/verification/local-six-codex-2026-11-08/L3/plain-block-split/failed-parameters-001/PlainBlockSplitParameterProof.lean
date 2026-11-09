module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockSplitCoverageProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.TiedLinearStatementChecks
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockSplitProof
open BlockRows PlainBlockSplit

/-- Universally quantified whole-block independence yields literal parameter
support inclusion, by testing one original name at a time. -/
theorem parameters_subset_of_independence (p q : Formula)
    (h : ∀ names : List Nat, ParametersIndependent names p → ParametersIndependent names q)
    (j : Nat) (hj : j ∈ q.parameters) : j ∈ p.parameters := by
  classical
  by_contra hnot
  have hin : ParametersIndependent [j] p := by
    intro k hk
    have he : k = j := List.mem_singleton.mp hk
    subst k
    exact hnot
  exact h [j] hin j (by simp) hj

theorem eliminate_parameter_support (i : Nat) (p : Formula) (j : Nat)
    (hj : j ∈ (TiedLinear.eliminate i p).parameters) : j ∈ p.parameters :=
  parameters_subset_of_independence p (TiedLinear.eliminate i p)
    (fun names h => TiedLinearProof.wholeBlockParameterIndependence names i p h) j hj

theorem nonnegative_parameter_support (i : Nat) (r : Row) (j : Nat)
    (hj : j ∈ (PlainMaximum.linearizeNonnegative i r).parameters) : j ∈ r.parameters :=
  parameters_subset_of_independence (.atom (.nonnegative r)) _
    (fun names h => PlainMaximumProof.wholeBlockParameterPreservation names r i h) j hj

theorem residue_parameter_support (m i : Nat) (r : Row) (j : Nat)
    (hj : j ∈ (PlainMaximumResidue.lowerAtom m i r).parameters) : j ∈ r.parameters :=
  parameters_subset_of_independence (.atom (.divisible m r)) _
    (fun names h => PlainMaximumResidueProof.wholeBlockParameterPreservation names r m i h) j hj

theorem substitution_parameter_support (p : Formula) (i : Nat) (t : Term) (j : Nat)
    (hj : j ∈ (p.substitute i t).parameters) : j ∈ p.parameters ∨ j ∈ t.variables := by
  classical
  by_cases hp : j ∈ p.parameters
  · exact Or.inl hp
  by_cases ht : j ∈ t.variables
  · exact Or.inr ht
  have hin : ParametersIndependent [j] p := by
    intro k hk
    have he : k = j := List.mem_singleton.mp hk
    subst k
    exact hp
  have hterm : ∀ k ∈ [j], k ∉ t.variables := by
    intro k hk
    have he : k = j := List.mem_singleton.mp hk
    subst k
    exact ht
  exact False.elim (BlockRowsProof.wholeBlockParameterIndependence [j] p i t hin hterm j (by simp) hj)

theorem rename_parameters (p : Formula) (i j : Nat) : (rename i j p).parameters = p.parameters := by
  induction p with
  | truth => rfl
  | falsity => rfl
  | atom a => cases a <;> rfl
  | negative p ih => exact ih
  | conjunction p q ihp ihq => simp only [rename, Formula.parameters, ihp, ihq]
  | disjunction p q ihp ihq => simp only [rename, Formula.parameters, ihp, ihq]

theorem all_parameter_support (ps : List Formula) (j : Nat) (hj : j ∈ (all ps).parameters) :
    ∃ p ∈ ps, j ∈ p.parameters := by
  induction ps with
  | nil => simp [all, Formula.parameters] at hj
  | cons p ps ih =>
    rcases List.mem_append.mp hj with h | h
    · exact ⟨p, List.mem_cons_self, h⟩
    · obtain ⟨q, hq, hjq⟩ := ih h
      exact ⟨q, List.mem_cons_of_mem _ hq, hjq⟩

theorem frame_parameters (bound : List Nat) (i : Nat) (p : Formula) :
    (frame bound i p).parameters = [] := by
  have hnone : ∀ j, j ∉ (frame bound i p).parameters := by
    intro j hj
    rcases List.mem_append.mp hj with hlo | hmax
    · simpa [lowerGuard, Formula.parameters, Atom.row, Row.parameters, Term.variables] using hlo
    · obtain ⟨q, hq, hjq⟩ := all_parameter_support _ j hmax
      obtain ⟨k, _, rfl⟩ := List.mem_map.mp hq
      simpa [strictMaximumGuard, Formula.parameters, Atom.row, Row.parameters, Term.variables] using hjq
  apply List.eq_nil_iff_forall_not_mem.mpr
  exact hnone

theorem outside_parameter_support (i : Nat) (p : Formula) (j : Nat)
    (hj : j ∈ (outside i p).parameters) : j ∈ p.parameters := by
  obtain ⟨q, hq, hjq⟩ := all_parameter_support _ j hj
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hq
  cases a with
  | nonnegative r =>
    exact atom_parameter_support p (.nonnegative r) ha j (outside_row_parameter_support i r j hjq)
  | divisible m r => simp [Formula.parameters] at hjq

theorem linearize_parameter_support (p : Formula) (i j : Nat)
    (hj : j ∈ (linearize i p).parameters) : j ∈ p.parameters := by
  induction p with
  | truth => simp [linearize, Formula.parameters] at hj
  | falsity => simp [linearize, Formula.parameters] at hj
  | atom a =>
    cases a with
    | nonnegative r => exact nonnegative_parameter_support i r j hj
    | divisible m r => exact residue_parameter_support m i r j hj
  | negative p ih => exact ih hj
  | conjunction p q ihp ihq =>
    rcases List.mem_append.mp hj with h | h
    · exact List.mem_append_left _ (ihp h)
    · exact List.mem_append_right _ (ihq h)
  | disjunction p q ihp ihq =>
    rcases List.mem_append.mp hj with h | h
    · exact List.mem_append_left _ (ihp h)
    · exact List.mem_append_right _ (ihq h)

theorem far_parameter_support (bound : List Nat) (p : Formula) (i j : Nat)
    (hj : j ∈ (TiedLinear.eliminate i
      (.conjunction (frame bound i p) (.conjunction (outside i p) (linearize i p)))).parameters) :
    j ∈ p.parameters := by
  have h := eliminate_parameter_support i
    (.conjunction (frame bound i p) (.conjunction (outside i p) (linearize i p))) j hj
  rcases List.mem_append.mp h with hf | h
  · rw [frame_parameters] at hf
    exact False.elim (List.not_mem_nil hf)
  · rcases List.mem_append.mp h with ho | hl
    · exact outside_parameter_support i p j ho
    · exact linearize_parameter_support p i j hl

theorem band_candidate_support (i : Nat) (r : Row) (d j : Nat) :
    j ∈ (bandCandidate i r d).variables ↔ j ∈ r.parameters := by
  simp only [bandCandidate, Term.variables, List.mem_append, List.not_mem_nil,
    or_false, PlainMaximumProof.boundary_support]

/-- No erased original bound name can leak back through a new parameter
constant: the parameter support monotonically decreases at EVERY branch. -/
theorem branch_parameter_support (bound : List Nat) (p : Formula) (s : State)
    (hs : s ∈ branches bound p) (j : Nat) (hj : j ∈ s.2.parameters) : j ∈ p.parameters := by
  change s ∈ ((small bound p ++ ties bound p) ++ bands bound p) ++ far bound p at hs
  rcases List.mem_append.mp hs with hleft | hfar
  · rcases List.mem_append.mp hleft with hleft | hbands
    · rcases List.mem_append.mp hleft with hsmall | hties
      · cases bound with
        | nil => simp [small] at hsmall
        | cons i rest =>
          obtain ⟨n, _, rfl⟩ := List.mem_map.mp hsmall
          rcases substitution_parameter_support p i (.numeral n) j hj with h | h
          · exact h
          · simp [Term.variables] at h
      · obtain ⟨i, _, hinner⟩ := List.mem_flatMap.mp hties
        obtain ⟨k, _, rfl⟩ := List.mem_map.mp hinner
        simpa only [rename_parameters] using hj
    · obtain ⟨i, _, hinner⟩ := List.mem_flatMap.mp hbands
      obtain ⟨a, ha, hatom⟩ := List.mem_flatMap.mp hinner
      cases a with
      | nonnegative r =>
        change s ∈ (if PlainMaximum.headCoefficient i r = 0 then [] else
          (List.range 5).map (fun d => (bound.erase i, p.substitute i (bandCandidate i r d)))) at hatom
        by_cases hz : PlainMaximum.headCoefficient i r = 0
        · simp only [if_pos hz, List.not_mem_nil] at hatom
        · rw [if_neg hz] at hatom
          obtain ⟨d, _, rfl⟩ := List.mem_map.mp hatom
          rcases substitution_parameter_support p i (bandCandidate i r d) j hj with h | h
          · exact h
          · exact atom_parameter_support p (.nonnegative r) ha j ((band_candidate_support i r d j).mp h)
      | divisible m r => exact False.elim (List.not_mem_nil hatom)
  · obtain ⟨i, _, rfl⟩ := List.mem_map.mp hfar
    exact far_parameter_support bound p i j hj

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockSplitProof
