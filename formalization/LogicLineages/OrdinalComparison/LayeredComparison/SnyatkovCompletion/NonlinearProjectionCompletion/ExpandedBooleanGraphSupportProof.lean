module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedBooleanGraphForestProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceRowsSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedBooleanGraphProof
open NormalForm

/-- Upper support is unconditional: an unsupported H graph is falsity, not
an excuse to assume that the original term was H-free. -/
theorem graph_support_upper (start : Nat) (t : Term) : ∀ i : Nat,
    i ∈ (ExpandedGraph.graph start t).variables →
      i ∈ t.variables ∨ i ∈ ExpandedGraph.allocated start t := by
  open ExpandedGraph ExpandedGraphProof in
  induction t generalizing start with
  | numeral n =>
      intro i hi
      simp only [graph, mem_equation_variables, SourceTermGraph.numeralRow, rowVariables,
        List.map_cons, List.map_nil, Summand.name, List.mem_singleton] at hi
      simp only [Term.variables, List.not_mem_nil, false_or, mem_allocated, nodeCount]
      omega
  | «variable» j =>
      intro i hi
      simp only [graph, mem_equation_variables, SourceTermGraph.variableRow, rowVariables,
        List.map_cons, List.map_nil, Summand.name, List.mem_cons, List.not_mem_nil, or_false] at hi
      simp only [Term.variables, List.mem_singleton, mem_allocated, nodeCount]
      omega
  | add a b iha ihb =>
      intro i hi
      have ha := iha start i
      have hb := ihb (start + nodeCount a) i
      have hpa := nodeCount_pos a
      have hpb := nodeCount_pos b
      simp only [graph, NormalForm.Formula.variables, List.mem_append, mem_equation_variables,
        SourceTermGraph.additionRow, rowVariables, List.map_cons, List.map_nil,
        Summand.name, List.mem_cons, List.not_mem_nil, or_false, output, nodeCount] at hi
      simp only [Term.variables, List.mem_append, mem_allocated, nodeCount] at ha hb ⊢
      rcases hi with h | h | h
      · rcases ha h with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr (by omega)
      · rcases hb h with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr (by omega)
      · exact Or.inr (by omega)
  | subtract a b iha ihb =>
      intro i hi
      have ha := iha start i
      have hb := ihb (start + nodeCount a) i
      have hpa := nodeCount_pos a
      have hpb := nodeCount_pos b
      simp only [graph, NormalForm.Formula.variables, List.mem_append,
        subtraction_variables, output, nodeCount] at hi
      simp only [Term.variables, List.mem_append, mem_allocated, nodeCount] at ha hb ⊢
      rcases hi with h | h | h
      · rcases ha h with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr (by omega)
      · rcases hb h with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr (by omega)
      · exact Or.inr (by omega)
  | multiply c a ih =>
      intro i hi
      have ha := ih start i
      have hpa := nodeCount_pos a
      simp only [graph, NormalForm.Formula.variables, List.mem_append, mem_equation_variables,
        multiplyRow, rowVariables, List.map_cons, List.map_nil, Summand.name,
        List.mem_cons, List.not_mem_nil, or_false, output, nodeCount] at hi
      simp only [Term.variables, mem_allocated, nodeCount] at ha ⊢
      rcases hi with h | h
      · rcases ha h with h | h
        · exact Or.inl h
        · exact Or.inr (by omega)
      · exact Or.inr (by omega)
  | divide c a ih =>
      intro i hi
      have ha := ih start i
      have hpa := nodeCount_pos a
      simp only [graph, NormalForm.Formula.variables, List.mem_append,
        division_variables, output, nodeCount] at hi
      simp only [Term.variables, mem_allocated, nodeCount] at ha ⊢
      rcases hi with h | h
      · rcases ha h with h | h
        · exact Or.inl h
        · exact Or.inr (by omega)
      · exact Or.inr (by omega)
  | phi a ih =>
      intro i hi
      have ha := ih start i
      have hpa := nodeCount_pos a
      simp only [graph, NormalForm.Formula.variables, List.mem_append, mem_equation_variables,
        SourceTermGraph.phiRow, rowVariables, List.map_cons, List.map_nil, Summand.name,
        List.mem_cons, List.not_mem_nil, or_false, output, nodeCount] at hi
      simp only [Term.variables, mem_allocated, nodeCount] at ha ⊢
      rcases hi with h | h
      · rcases ha h with h | h
        · exact Or.inl h
        · exact Or.inr (by omega)
      · exact Or.inr (by omega)
  | phiInverse a ih =>
      intro i hi
      have ha := ih start i
      have hpa := nodeCount_pos a
      simp only [graph, NormalForm.Formula.variables, List.mem_append,
        inverse_variables, output, nodeCount] at hi
      simp only [Term.variables, mem_allocated, nodeCount] at ha ⊢
      rcases hi with h | h
      · rcases ha h with h | h
        · exact Or.inl h
        · exact Or.inr (by omega)
      · exact Or.inr (by omega)
  | hyper a ih => intro i hi; exact False.elim (List.not_mem_nil hi)
  | hyperInverse a ih => intro i hi; exact False.elim (List.not_mem_nil hi)

open ExpandedBooleanGraph in
theorem predicate_support (p : Matrix) (s : Nat) : ∀ i : Nat,
    i ∈ (predicate s p).variables → i ∈ ExpandedGraph.allocated s (forest p) := by
  open ExpandedGraph ExpandedGraphProof in
  induction p generalizing s with
  | truth => intro i hi; exact False.elim (List.not_mem_nil hi)
  | falsity => intro i hi; exact False.elim (List.not_mem_nil hi)
  | equal a b =>
      intro i hi
      have hpa := nodeCount_pos a
      have hpb := nodeCount_pos b
      simp only [predicate, SourceRowsSupportProof.relation_variables, output] at hi
      simp only [forest, mem_allocated, nodeCount]
      omega
  | less a b =>
      intro i hi
      have hpa := nodeCount_pos a
      have hpb := nodeCount_pos b
      simp only [predicate, SourceRowsSupportProof.relation_variables, output] at hi
      simp only [forest, mem_allocated, nodeCount]
      omega
  | divisible m a =>
      intro i hi
      have he : i = output s a := by
        by_cases hm : m = 0
        · simpa only [predicate, if_pos hm, mem_equation_variables, rowVariables,
            List.map_cons, List.map_nil, Summand.name, List.mem_singleton] using hi
        · simpa only [predicate, if_neg hm, NormalForm.Formula.variables, NormalForm.Atom.row,
            rowVariables, List.map_cons, List.map_nil, Summand.name, List.mem_singleton] using hi
      subst i
      exact output_mem_allocated s a
  | negative p ih => exact ih s
  | conjunction p q ihp ihq =>
      intro i hi
      rcases List.mem_append.mp hi with hp | hq
      · have h := (mem_allocated s (forest p) i).mp (ihp s i hp)
        rw [mem_allocated]
        simp only [forest, nodeCount]
        omega
      · have h := (mem_allocated (s + nodeCount (forest p)) (forest q) i).mp
          (ihq (s + nodeCount (forest p)) i hq)
        rw [mem_allocated]
        simp only [forest, nodeCount]
        omega
  | disjunction p q ihp ihq =>
      intro i hi
      rcases List.mem_append.mp hi with hp | hq
      · have h := (mem_allocated s (forest p) i).mp (ihp s i hp)
        rw [mem_allocated]
        simp only [forest, nodeCount]
        omega
      · have h := (mem_allocated (s + nodeCount (forest p)) (forest q) i).mp
          (ihq (s + nodeCount (forest p)) i hq)
        rw [mem_allocated]
        simp only [forest, nodeCount]
        omega

open ExpandedBooleanGraph in
theorem originalGraphNameSupport : ExpandedBooleanGraphTargets.OriginalGraphNameSupport := by
  intro bound p j hj
  rcases List.mem_append.mp hj with hg | hp
  · have h := graph_support_upper (startFor bound p) (forest p) j hg
    simpa only [ExpandedBooleanGraph.allocated, literalForestSupport p] using h
  · exact Or.inr (predicate_support p (startFor bound p) j hp)

#print axioms graph_support_upper
#print axioms predicate_support
#print axioms originalGraphNameSupport
end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedBooleanGraphProof
