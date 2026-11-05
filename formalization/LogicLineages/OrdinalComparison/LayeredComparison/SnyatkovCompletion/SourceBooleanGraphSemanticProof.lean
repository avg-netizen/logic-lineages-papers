module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceBooleanGraphTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceRowsSemanticProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainLinearCleanupSemanticProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceBooleanGraphProof
open CommonLayerSyntax NormalForm SourceTermGraph SourceBooleanGraph
open SourceTermGraphSupportProof SourceTermGraphSemanticProof SourceTermGraphExistentialProof

theorem literalForestVariables : SourceBooleanGraphTargets.LiteralForestVariables := by
  intro p
  induction p with
  | equal a b => intro _; rfl
  | less a b => intro _; rfl
  | negative p ih => exact ih
  | conjunction p q ihp ihq =>
      intro h
      have hh := Bool.and_eq_true_iff.mp h
      simp only [forest, BaseTerm.variables, SourceFormula.variables, ihp hh.1, ihq hh.2]
  | existsNat i p ih => intro h; cases h

theorem source_eval_congr (p : SourceFormula) (hp : test p = true) (ν σ : Nat → Nat)
    (h : ∀ i ∈ p.variables, ν i = σ i) : p.eval ν ↔ p.eval σ := by
  induction p with
  | equal a b =>
      have ha := source_value_congr a ν σ (fun i hi => h i (List.mem_append_left _ hi))
      have hb := source_value_congr b ν σ (fun i hi => h i (List.mem_append_right _ hi))
      simp only [SourceFormula.eval, ha, hb]
  | less a b =>
      have ha := source_value_congr a ν σ (fun i hi => h i (List.mem_append_left _ hi))
      have hb := source_value_congr b ν σ (fun i hi => h i (List.mem_append_right _ hi))
      simp only [SourceFormula.eval, ha, hb]
  | negative p ih => exact not_congr (ih hp h)
  | conjunction p q ihp ihq =>
      have hh := Bool.and_eq_true_iff.mp hp
      exact and_congr (ihp hh.1 (fun i hi => h i (List.mem_append_left _ hi)))
        (ihq hh.2 (fun i hi => h i (List.mem_append_right _ hi)))
  | existsNat i p ih => cases hp

theorem actualPredicateInterpretation : SourceBooleanGraphTargets.ActualPredicateInterpretation := by
  intro p
  induction p with
  | equal a b =>
      intro s ν _ hg
      obtain ⟨ha, hb, _⟩ := (graph_add s a b ν).mp hg
      have ea := graphSoundness s a ν ha
      have eb := graphSoundness (s + nodeCount a) b ν hb
      simpa only [predicate, SourceFormula.eval, Bool.false_eq_true, ↓reduceIte, ea, eb] using
        SourceRowsSemanticProof.relation_eval false (output s a) (output (s + nodeCount a) b) ν
  | less a b =>
      intro s ν _ hg
      obtain ⟨ha, hb, _⟩ := (graph_add s a b ν).mp hg
      have ea := graphSoundness s a ν ha
      have eb := graphSoundness (s + nodeCount a) b ν hb
      simpa only [predicate, SourceFormula.eval, ↓reduceIte, ea, eb] using
        SourceRowsSemanticProof.relation_eval true (output s a) (output (s + nodeCount a) b) ν
  | negative p ih =>
      intro s ν hp hg
      exact not_congr (ih s ν hp hg)
  | conjunction p q ihp ihq =>
      intro s ν hp hg
      have hh := Bool.and_eq_true_iff.mp hp
      obtain ⟨ha, hb, _⟩ := (graph_add s (forest p) (forest q) ν).mp hg
      exact and_congr (ihp s ν hh.1 ha) (ihq (s + nodeCount (forest p)) ν hh.2 hb)
  | existsNat i p ih => intro s ν hp; cases hp

theorem start_fresh (p : SourceFormula) : Fresh (start p) (forest p) :=
  SourceRowsSupportProof.term_variable_lt_bound (forest p)

theorem actualExistentialMatrix : SourceBooleanGraphTargets.ActualExistentialMatrix := by
  intro p ν hp
  rw [existsPrefix_iff_frame]
  have hf := start_fresh p
  have he (σ : Nat → Nat) (hframe : ∀ i, i ∉ allocated (start p) (forest p) → σ i = ν i) :
      p.eval σ ↔ p.eval ν := by
    apply source_eval_congr p hp σ ν
    intro i hi
    apply hframe i
    intro hm
    have hv : i ∈ (forest p).variables := by rw [literalForestVariables p hp]; exact hi
    have hl := hf i hv
    have hr := (mem_allocated (start p) (forest p) i).mp hm
    omega
  constructor
  · rintro ⟨σ, hframe, hmatrix⟩
    change (graph (start p) (forest p)).eval σ ∧ (predicate (start p) p).eval σ at hmatrix
    exact (he σ hframe).mp ((actualPredicateInterpretation p (start p) σ hp hmatrix.1).mp hmatrix.2)
  · intro hs
    obtain ⟨σ, hframe, hgraph, _⟩ := totalGraphRealization (start p) (forest p) ν hf
    refine ⟨σ, hframe, ?_⟩
    change (graph (start p) (forest p)).eval σ ∧ (predicate (start p) p).eval σ
    exact ⟨hgraph, (actualPredicateInterpretation p (start p) σ hp hgraph).mpr ((he σ hframe).mpr hs)⟩

theorem actualSatisfiabilityTranslation : SourceBooleanGraphTargets.ActualSatisfiabilityTranslation := by
  intro p hp
  rw [← PlainLinearCleanupProof.prefix_satisfiable (allocated (start p) (forest p)) (compile p)]
  exact exists_congr (fun ν => actualExistentialMatrix p ν hp)

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceBooleanGraphProof
