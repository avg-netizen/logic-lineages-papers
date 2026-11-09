module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.WholeBoundInitializationTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.BlockRowsSubstitutionProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.WholeBoundInitializationProof
open WholeBoundInitialization

theorem entries_occurrences (bound : List Nat) (positive negative : Term)
    (es : List (Int × NormalForm.Summand)) :
    (entries bound positive negative es).2 = es.filter (fun a => bound.contains a.2.name) := by
  induction es with
  | nil => rfl
  | cons a es ih =>
      by_cases h : bound.contains a.2.name = true <;>
        simp only [entries, List.filter_cons, h, Bool.false_eq_true, reduceIte, ih]

theorem literalOccurrencePartition : WholeBoundInitializationTargets.LiteralOccurrencePartition :=
  fun bound r => entries_occurrences bound _ _ r.2

theorem entries_parameters (bound : List Nat) (positive negative : Term)
    (es : List (Int × NormalForm.Summand)) (j : Nat) :
    j ∈ (entries bound positive negative es).parameters ↔
      j ∈ positive.variables ∨ j ∈ negative.variables ∨
        (j ∈ es.map (fun a => a.2.name) ∧ j ∉ bound) := by
  induction es with
  | nil => simp [entries, BlockRows.Row.parameters]
  | cons a es ih =>
      by_cases h : bound.contains a.2.name = true
      · have hin : a.2.name ∈ bound := by simpa using h
        simp only [entries, if_pos h, List.map_cons, List.mem_cons]
        change (j ∈ (entries bound positive negative es).parameters ↔
          j ∈ positive.variables ∨ j ∈ negative.variables ∨
            ((j = a.2.name ∨ j ∈ es.map (fun a => a.2.name)) ∧ j ∉ bound))
        rw [ih]
        by_cases hj : j = a.2.name
        · subst j; simp [hin]
        · simp [hj]
      · have hout : a.2.name ∉ bound := by simpa using h
        have he : j ∈ (entries bound positive negative (a :: es)).parameters ↔
            j = a.2.name ∨ j ∈ (entries bound positive negative es).parameters := by
          simp only [entries, if_neg h, BlockRows.Row.parameters, Term.variables,
            List.mem_append, BlockRowsProof.original_summand_variables]
          tauto
        rw [he, ih]
        simp only [List.map_cons, List.mem_cons]
        by_cases hj : j = a.2.name
        · subst j; simp [hout]
        · simp [hj]

theorem literalParameterSupport : WholeBoundInitializationTargets.LiteralParameterSupport := by
  intro bound r j
  simpa only [row, Term.variables, List.not_mem_nil, false_or, NormalForm.rowVariables] using
    entries_parameters bound (.numeral r.1.toNat) (.numeral (-r.1).toNat) r.2 j

theorem row_name_support (bound : List Nat) (r : NormalForm.Row) (j : Nat) :
    j ∈ (row bound r).variables ↔ j ∈ NormalForm.rowVariables r := by
  have he : j ∈ ((row bound r).2.map (fun a => a.2.name)) ↔
      j ∈ NormalForm.rowVariables r ∧ j ∈ bound := by
    rw [literalOccurrencePartition bound r]
    simp only [NormalForm.rowVariables, List.mem_map, List.mem_filter]
    constructor
    · rintro ⟨a, ⟨ha, hb⟩, hj⟩
      subst j
      exact ⟨⟨a, ha, rfl⟩, by simpa using hb⟩
    · rintro ⟨⟨a, ha, hj⟩, hb⟩
      subst j
      exact ⟨a, ⟨ha, by simpa using hb⟩, rfl⟩
  rw [BlockRows.Row.variables, List.mem_append]
  change (j ∈ (row bound r).parameters ∨
    j ∈ (row bound r).2.map (fun a => a.2.name)) ↔ _
  rw [literalParameterSupport bound r j, he]
  by_cases h : j ∈ bound <;> simp [h]

theorem formula_parameters (bound : List Nat) (p : NormalForm.Formula) (j : Nat) :
    j ∈ («initialize» bound p).parameters ↔ j ∈ p.variables ∧ j ∉ bound := by
  induction p with
  | truth => simp [«initialize», BlockRows.Formula.parameters, NormalForm.Formula.variables]
  | falsity => simp [«initialize», BlockRows.Formula.parameters, NormalForm.Formula.variables]
  | atom a => cases a <;> exact literalParameterSupport bound _ j
  | negative p ih => exact ih
  | conjunction p q ihp ihq =>
      simp only [«initialize», BlockRows.Formula.parameters, NormalForm.Formula.variables,
        List.mem_append, ihp, ihq]
      tauto
  | disjunction p q ihp ihq =>
      simp only [«initialize», BlockRows.Formula.parameters, NormalForm.Formula.variables,
        List.mem_append, ihp, ihq]
      tauto

theorem wholeBoundParameterIndependence : WholeBoundInitializationTargets.WholeBoundParameterIndependence := by
  intro bound p i hi hp
  exact ((formula_parameters bound p i).mp hp).2 hi

theorem exactOriginalNameSupport : WholeBoundInitializationTargets.ExactOriginalNameSupport := by
  intro bound p j
  induction p with
  | truth => rfl
  | falsity => rfl
  | atom a => cases a <;> exact row_name_support bound _ j
  | negative p ih => exact ih
  | conjunction p q ihp ihq =>
      simpa only [«initialize», BlockRows.Formula.variables, NormalForm.Formula.variables,
        List.mem_append] using or_congr ihp ihq
  | disjunction p q ihp ihq =>
      simpa only [«initialize», BlockRows.Formula.variables, NormalForm.Formula.variables,
        List.mem_append] using or_congr ihp ihq

#print axioms entries_occurrences
#print axioms literalOccurrencePartition
#print axioms entries_parameters
#print axioms literalParameterSupport
#print axioms row_name_support
#print axioms formula_parameters
#print axioms wholeBoundParameterIndependence
#print axioms exactOriginalNameSupport
end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.WholeBoundInitializationProof
