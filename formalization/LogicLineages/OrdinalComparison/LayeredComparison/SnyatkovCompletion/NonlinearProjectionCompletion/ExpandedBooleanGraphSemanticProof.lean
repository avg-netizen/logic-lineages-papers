module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedBooleanGraphForestProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphRealizationProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceRowsSemanticProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedBooleanGraphProof
open ExpandedBooleanGraph NormalForm

theorem divisible_predicate (m s : Nat) (a : Term) (ν : Nat → Nat) :
    (predicate s (.divisible m a)).eval ν ↔ m ∣ ν (ExpandedGraph.output s a) := by
  by_cases hm : m = 0
  · subst m
    simp [predicate, ExpandedGraphProof.equation_eval, rowValue, Summand.term, Term.value]
  · have he : m - 1 + 1 = m := by omega
    simp only [predicate, if_neg hm, NormalForm.Formula.eval, NormalForm.Atom.eval,
      rowValue, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Summand.term, Term.value, one_mul, add_zero, zero_add, he, Int.natCast_dvd, Int.natAbs_natCast]

theorem actualPredicateInterpretation : ExpandedBooleanGraphTargets.ActualPredicateInterpretation := by
  intro p
  induction p with
  | truth => intro s ν hp hg; rfl
  | falsity => intro s ν hp hg; rfl
  | equal a b =>
      intro s ν hp hg
      have hh := Bool.and_eq_true_iff.mp hp
      obtain ⟨ha, hb, _⟩ := (ExpandedGraphProof.graph_add s a b ν).mp hg
      have ea := ExpandedGraphProof.graphSoundness s a ν hh.1 ha
      have eb := ExpandedGraphProof.graphSoundness (s + ExpandedGraph.nodeCount a) b ν hh.2 hb
      simpa only [predicate, Matrix.eval, Bool.false_eq_true, ↓reduceIte, ea, eb] using
        SourceRowsSemanticProof.relation_eval false (ExpandedGraph.output s a)
          (ExpandedGraph.output (s + ExpandedGraph.nodeCount a) b) ν
  | less a b =>
      intro s ν hp hg
      have hh := Bool.and_eq_true_iff.mp hp
      obtain ⟨ha, hb, _⟩ := (ExpandedGraphProof.graph_add s a b ν).mp hg
      have ea := ExpandedGraphProof.graphSoundness s a ν hh.1 ha
      have eb := ExpandedGraphProof.graphSoundness (s + ExpandedGraph.nodeCount a) b ν hh.2 hb
      simpa only [predicate, Matrix.eval, ↓reduceIte, ea, eb] using
        SourceRowsSemanticProof.relation_eval true (ExpandedGraph.output s a)
          (ExpandedGraph.output (s + ExpandedGraph.nodeCount a) b) ν
  | divisible m a =>
      intro s ν hp hg
      have ea := ExpandedGraphProof.graphSoundness s a ν hp hg
      simpa only [ea, Matrix.eval] using divisible_predicate m s a ν
  | negative p ih =>
      intro s ν hp hg
      exact not_congr (ih s ν hp hg)
  | conjunction p q ihp ihq =>
      intro s ν hp hg
      have hh := Bool.and_eq_true_iff.mp hp
      obtain ⟨ha, hb, _⟩ := (ExpandedGraphProof.graph_add s (forest p) (forest q) ν).mp hg
      exact and_congr (ihp s ν hh.1 ha)
        (ihq (s + ExpandedGraph.nodeCount (forest p)) ν hh.2 hb)
  | disjunction p q ihp ihq =>
      intro s ν hp hg
      have hh := Bool.and_eq_true_iff.mp hp
      obtain ⟨ha, hb, _⟩ := (ExpandedGraphProof.graph_add s (forest p) (forest q) ν).mp hg
      exact or_congr (ihp s ν hh.1 ha)
        (ihq (s + ExpandedGraph.nodeCount (forest p)) ν hh.2 hb)

theorem actualExpandedMatrixGraph : ExpandedBooleanGraphTargets.ActualExpandedMatrixGraph := by
  intro bound p ν hp
  rw [SourceTermGraphExistentialProof.existsPrefix_iff_frame]
  have he (σ : Nat → Nat)
      (hframe : ∀ i, i ∉ allocated bound p → σ i = ν i) : p.eval σ ↔ p.eval ν := by
    apply matrix_eval_congr p σ ν
    intro i hi
    apply hframe i
    intro hm
    exact (exactFreshGraphNames bound p).2 i hm |>.2 hi
  constructor
  · rintro ⟨σ, hframe, hmatrix⟩
    change (ExpandedGraph.graph (startFor bound p) (forest p)).eval σ ∧
      (predicate (startFor bound p) p).eval σ at hmatrix
    exact (he σ hframe).mp
      ((actualPredicateInterpretation p (startFor bound p) σ hp hmatrix.1).mp hmatrix.2)
  · intro hs
    obtain ⟨σ, hframe, hgraph, _⟩ := ExpandedGraphProof.totalGraphRealization
      (startFor bound p) (forest p) ν (hFreeOriginalForest p hp) (start_fresh bound p)
    refine ⟨σ, hframe, ?_⟩
    change (ExpandedGraph.graph (startFor bound p) (forest p)).eval σ ∧
      (predicate (startFor bound p) p).eval σ
    exact ⟨hgraph, (actualPredicateInterpretation p (startFor bound p) σ hp hgraph).mpr
      ((he σ hframe).mpr hs)⟩

#print axioms divisible_predicate
#print axioms actualPredicateInterpretation
#print axioms actualExpandedMatrixGraph
end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedBooleanGraphProof
