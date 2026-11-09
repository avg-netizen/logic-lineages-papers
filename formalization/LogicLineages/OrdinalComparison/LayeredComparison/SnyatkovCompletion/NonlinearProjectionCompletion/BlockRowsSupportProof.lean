module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.BlockRowsSubstitutionProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.BlockRowsProof
open BlockRows

private theorem entries_occurrences (i : Nat) (replacement positive negative : Term)
    (entries : List (Int × NormalForm.Summand)) :
    (substituteEntries i replacement positive negative entries).2 =
      entries.filter (fun a => a.2.name != i) := by
  induction entries with
  | nil => rfl
  | cons a entries ih =>
    by_cases hs : a.2.name = i <;> simp [substituteEntries, hs, ih]

theorem exactRemainingOccurrences : BlockRowsTargets.ExactRemainingOccurrences := by
  intro r i replacement
  exact entries_occurrences i replacement (r.1.1.substitute i replacement)
    (r.1.2.substitute i replacement) r.2

private theorem moved_support_logic (P N E I R : Prop) (i j : Nat) :
    (R ∨ P ∨ N ∨ (E ∧ j ≠ i) ∨ (I ∧ R)) ↔
      P ∨ N ∨ ((j = i ∨ E) ∧ j ≠ i) ∨ R := by
  by_cases h : j = i <;> simp [h] <;> tauto

private theorem retained_support_logic (P N E I R : Prop) (i j name : Nat)
    (hne : name ≠ i) :
    (j = name ∨ P ∨ N ∨ (E ∧ j ≠ i) ∨ (I ∧ R)) ↔
      P ∨ N ∨ ((j = name ∨ E) ∧ j ≠ i) ∨ (I ∧ R) := by
  by_cases h : j = name
  · subst j
    simp only [hne, not_false_eq_true, and_true, eq_self_iff_true, true_or]
    tauto
  · simp only [h, false_or]

private theorem entries_support (i : Nat) (replacement positive negative : Term)
    (entries : List (Int × NormalForm.Summand)) (j : Nat) :
    j ∈ (substituteEntries i replacement positive negative entries).variables ↔
      j ∈ positive.variables ∨ j ∈ negative.variables ∨
        (j ∈ entries.map (fun a => a.2.name) ∧ j ≠ i) ∨
        (i ∈ entries.map (fun a => a.2.name) ∧ j ∈ replacement.variables) := by
  induction entries with
  | nil => simp [substituteEntries, Row.variables]
  | cons a entries ih =>
    by_cases hs : a.2.name = i
    · have hm := moved_summand_variables a.2 i replacement hs j
      have he : j ∈ (substituteEntries i replacement positive negative (a :: entries)).variables ↔
          j ∈ replacement.variables ∨
            j ∈ (substituteEntries i replacement positive negative entries).variables := by
        simp only [substituteEntries, if_pos hs, Row.variables, Term.variables, List.mem_append, hm]
        tauto
      rw [he, ih]
      simp only [List.map_cons, List.mem_cons, hs, eq_self_iff_true, true_or, true_and]
      exact moved_support_logic _ _ _ _ _ i j
    · have he : j ∈ (substituteEntries i replacement positive negative (a :: entries)).variables ↔
          j = a.2.name ∨
            j ∈ (substituteEntries i replacement positive negative entries).variables := by
        simp only [substituteEntries, if_neg hs, Row.variables, List.map_cons, List.mem_cons, List.mem_append]
        tauto
      rw [he, ih]
      have hneq : i ≠ a.2.name := Ne.symm hs
      simp only [List.map_cons, List.mem_cons, hneq, false_or]
      exact retained_support_logic _ _ _ _ _ i j a.2.name hs

theorem row_support (r : Row) (i : Nat) (replacement : Term) (j : Nat) :
    j ∈ (r.substitute i replacement).variables ↔
      (j ∈ r.variables ∧ j ≠ i) ∨ (i ∈ r.variables ∧ j ∈ replacement.variables) := by
  rw [Row.substitute, entries_support]
  simp only [WindowProof.term_support, Row.variables, List.mem_append]
  tauto

theorem exactOriginalNameSupport : BlockRowsTargets.ExactOriginalNameSupport := by
  intro p i replacement j
  induction p with
  | truth => simp [Formula.substitute, Formula.variables]
  | falsity => simp [Formula.substitute, Formula.variables]
  | atom a => cases a <;> exact row_support _ i replacement j
  | negative p ih => exact ih
  | conjunction p q ihp ihq =>
    simp only [Formula.substitute, Formula.variables, List.mem_append, ihp, ihq]
    tauto
  | disjunction p q ihp ihq =>
    simp only [Formula.substitute, Formula.variables, List.mem_append, ihp, ihq]
    tauto

private theorem entries_parameter_support (i : Nat) (replacement positive negative : Term)
    (entries : List (Int × NormalForm.Summand)) (j : Nat) :
    j ∈ (substituteEntries i replacement positive negative entries).parameters →
      j ∈ positive.variables ∨ j ∈ negative.variables ∨ j ∈ replacement.variables := by
  induction entries with
  | nil =>
    simp only [substituteEntries, Row.parameters, List.mem_append]
    tauto
  | cons a entries ih =>
    by_cases hs : a.2.name = i
    · have hm := moved_summand_variables a.2 i replacement hs j
      have he : j ∈ (substituteEntries i replacement positive negative (a :: entries)).parameters ↔
          j ∈ replacement.variables ∨
            j ∈ (substituteEntries i replacement positive negative entries).parameters := by
        simp only [substituteEntries, if_pos hs, Row.parameters, Term.variables, List.mem_append, hm]
        tauto
      rw [he]
      tauto
    · simpa only [substituteEntries, if_neg hs, Row.parameters] using ih

private theorem row_parameter_support (r : Row) (i : Nat) (replacement : Term) (j : Nat)
    (hj : j ∈ (r.substitute i replacement).parameters) :
    j ∈ r.parameters ∨ j ∈ replacement.variables := by
  have h := entries_parameter_support i replacement (r.1.1.substitute i replacement)
    (r.1.2.substitute i replacement) r.2 j hj
  simp only [WindowProof.term_support] at h
  simp only [Row.parameters, List.mem_append]
  tauto

private theorem formula_parameter_support (p : Formula) (i : Nat) (replacement : Term) (j : Nat) :
    j ∈ (p.substitute i replacement).parameters →
      j ∈ p.parameters ∨ j ∈ replacement.variables := by
  induction p with
  | truth => simp [Formula.substitute, Formula.parameters]
  | falsity => simp [Formula.substitute, Formula.parameters]
  | atom a => cases a <;> exact row_parameter_support _ i replacement j
  | negative p ih => exact ih
  | conjunction p q ihp ihq =>
    simp only [Formula.substitute, Formula.parameters, List.mem_append]
    tauto
  | disjunction p q ihp ihq =>
    simp only [Formula.substitute, Formula.parameters, List.mem_append]
    tauto

theorem wholeBlockParameterIndependence : BlockRowsTargets.WholeBlockParameterIndependence := by
  intro bound p i replacement hp hr j hj hnew
  rcases formula_parameter_support p i replacement j hnew with hold | hreplacement
  · exact hp j hj hold
  · exact hr j hj hreplacement

theorem exactOriginalGuardedDomains : BlockRowsTargets.ExactOriginalGuardedDomains := by
  intro a i replacement ν
  rw [actualExpandedCompilation, formula_substitution, actualOriginalFormulaEmbedding]
  change (NormalForm.domainFormula a.row).eval (Function.update ν i (replacement.value ν)) ∧
      a.eval (Function.update ν i (replacement.value ν)) ↔ _
  exact and_congr
    (NormalFormSemanticProof.exactOriginalRowDomains a.row (Function.update ν i (replacement.value ν)))
    Iff.rfl

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.BlockRowsProof
