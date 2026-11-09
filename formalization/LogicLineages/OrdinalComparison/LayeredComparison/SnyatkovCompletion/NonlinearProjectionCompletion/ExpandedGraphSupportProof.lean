module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphAllocationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphProof
open ExpandedGraph NormalForm

theorem mem_equation_variables (r : NormalForm.Row) (i : Nat) :
    i ∈ (ExpandedGraph.equation r).variables ↔ i ∈ rowVariables r :=
  SourceTermGraphSupportProof.mem_equation_variables r i

theorem subtraction_variables (z x y i : Nat) :
    i ∈ (subtraction z x y).variables ↔ i = z ∨ i = x ∨ i = y := by
  simp [subtraction, nonnegative, NormalForm.Formula.variables, NormalForm.Atom.row,
    mem_equation_variables, rowVariables, Summand.name, or_assoc, or_left_comm, or_comm]

theorem division_variables (z x c i : Nat) :
    i ∈ (division z x c).variables ↔ i = z ∨ (c ≠ 0 ∧ i = x) := by
  by_cases hc : c = 0
  · simp [division, hc, mem_equation_variables, rowVariables, Summand.name]
  · simp [division, hc, nonnegative, NormalForm.Formula.variables, NormalForm.Atom.row,
      rowVariables, Summand.name, or_assoc, or_left_comm, or_comm]

theorem inverse_variables (u z x i : Nat) :
    i ∈ (inverse u z x).variables ↔ i = u ∨ i = z ∨ i = x := by
  simp [inverse, nonnegative, NormalForm.Formula.variables, NormalForm.Atom.row,
    mem_equation_variables, rowVariables, Summand.name, or_assoc, or_left_comm, or_comm]

theorem exactGraphSupport : ExpandedGraphTargets.ExactGraphSupport := by
  intro start t
  induction t generalizing start with
  | numeral n =>
      intro hf i
      simp only [graph, mem_equation_variables, SourceTermGraph.numeralRow, rowVariables,
        List.map_cons, List.map_nil, Summand.name, Term.variables, List.not_mem_nil,
        false_or, List.mem_singleton, mem_allocated, nodeCount]
      omega
  | «variable» j =>
      intro hf i
      simp only [graph, mem_equation_variables, SourceTermGraph.variableRow, rowVariables,
        List.map_cons, List.map_nil, Summand.name, Term.variables, List.mem_cons,
        List.not_mem_nil, or_false, mem_allocated, nodeCount]
      omega
  | add a b iha ihb =>
      intro hf i
      have hfa := (Bool.and_eq_true_iff.mp hf).1
      have hfb := (Bool.and_eq_true_iff.mp hf).2
      have ha := nodeCount_pos a
      have hb := nodeCount_pos b
      simp only [graph, NormalForm.Formula.variables, List.mem_append, mem_equation_variables, SourceTermGraph.additionRow, rowVariables, List.map_cons, List.map_nil, Summand.name, List.mem_cons, List.not_mem_nil, or_false]
      rw [iha start hfa i, ihb (start + nodeCount a) hfb i]
      simp only [Term.variables, List.mem_append, mem_allocated, nodeCount, output]
      by_cases hia : i ∈ a.variables <;> by_cases hib : i ∈ b.variables <;>
        simp only [hia, hib, true_or, or_true, false_or, or_false] <;> omega
  | subtract a b iha ihb =>
      intro hf i
      have hfa := (Bool.and_eq_true_iff.mp hf).1
      have hfb := (Bool.and_eq_true_iff.mp hf).2
      have ha := nodeCount_pos a
      have hb := nodeCount_pos b
      simp only [graph, NormalForm.Formula.variables, List.mem_append, subtraction_variables]
      rw [iha start hfa i, ihb (start + nodeCount a) hfb i]
      simp only [Term.variables, List.mem_append, mem_allocated, nodeCount, output]
      by_cases hia : i ∈ a.variables <;> by_cases hib : i ∈ b.variables <;>
        simp only [hia, hib, true_or, or_true, false_or, or_false] <;> omega
  | multiply c a ih =>
      intro hf i
      have ha := nodeCount_pos a
      simp only [graph, NormalForm.Formula.variables, List.mem_append, mem_equation_variables, multiplyRow, rowVariables, List.map_cons, List.map_nil, Summand.name, List.mem_cons, List.not_mem_nil, or_false]
      rw [ih start hf i]
      simp only [Term.variables, mem_allocated, nodeCount, output]
      by_cases hia : i ∈ a.variables <;>
        simp only [hia, true_or, or_true, false_or, or_false] <;> omega
  | divide c a ih =>
      intro hf i
      have ha := nodeCount_pos a
      simp only [graph, NormalForm.Formula.variables, List.mem_append, division_variables]
      rw [ih start hf i]
      simp only [Term.variables, mem_allocated, nodeCount, output]
      by_cases hia : i ∈ a.variables <;>
        simp only [hia, true_or, or_true, false_or, or_false] <;> omega
  | phi a ih =>
      intro hf i
      have ha := nodeCount_pos a
      simp only [graph, NormalForm.Formula.variables, List.mem_append, mem_equation_variables, SourceTermGraph.phiRow, rowVariables, List.map_cons, List.map_nil, Summand.name, List.mem_cons, List.not_mem_nil, or_false]
      rw [ih start hf i]
      simp only [Term.variables, mem_allocated, nodeCount, output]
      by_cases hia : i ∈ a.variables <;>
        simp only [hia, true_or, or_true, false_or, or_false] <;> omega
  | phiInverse a ih =>
      intro hf i
      have ha := nodeCount_pos a
      simp only [graph, NormalForm.Formula.variables, List.mem_append, inverse_variables]
      rw [ih start hf i]
      simp only [Term.variables, mem_allocated, nodeCount, output]
      by_cases hia : i ∈ a.variables <;>
        simp only [hia, true_or, or_true, false_or, or_false] <;> omega
  | hyper a ih => intro hf; simp only [PlainBlockSplit.termHFree, Bool.false_eq_true] at hf
  | hyperInverse a ih => intro hf; simp only [PlainBlockSplit.termHFree, Bool.false_eq_true] at hf

theorem term_value_congr (t : Term) (ν σ : Nat → Nat)
    (h : ∀ i ∈ t.variables, ν i = σ i) : t.value ν = t.value σ := by
  revert h
  induction t with
  | numeral n => intro h; rfl
  | «variable» i => intro h; exact h i (List.mem_singleton_self _)
  | add a b iha ihb =>
      intro h
      exact congrArg₂ (· + ·) (iha (fun i hi => h i (List.mem_append_left _ hi)))
        (ihb (fun i hi => h i (List.mem_append_right _ hi)))
  | subtract a b iha ihb =>
      intro h
      exact congrArg₂ (· - ·) (iha (fun i hi => h i (List.mem_append_left _ hi)))
        (ihb (fun i hi => h i (List.mem_append_right _ hi)))
  | multiply c a ih => intro h; exact congrArg (fun n => c * n) (ih h)
  | divide c a ih => intro h; exact congrArg (fun n => n / c) (ih h)
  | phi a ih => intro h; exact congrArg Phi (ih h)
  | hyper a ih => intro h; exact congrArg FixedSeedControlResidue.H (ih h)
  | phiInverse a ih => intro h; exact congrArg SnyatkovInverse.phiInverse (ih h)
  | hyperInverse a ih => intro h; exact congrArg SnyatkovInverse.hyperInverse (ih h)

theorem graph_eval_congr (start : Nat) (t : Term) (ν σ : Nat → Nat)
    (hf : PlainBlockSplit.termHFree t = true)
    (h : ∀ i, i ∈ t.variables ∨ i ∈ allocated start t → ν i = σ i) :
    (graph start t).eval ν ↔ (graph start t).eval σ :=
  SourceTermGraphSupportProof.formula_eval_congr (graph start t) ν σ
    (fun i hi => h i ((exactGraphSupport start t hf i).mp hi))

#print axioms mem_equation_variables
#print axioms subtraction_variables
#print axioms division_variables
#print axioms inverse_variables
#print axioms exactGraphSupport
#print axioms term_value_congr
#print axioms graph_eval_congr
end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphProof
