module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceRowsSupportProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceTermGraphExistentialProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceRowsSemanticProof
open CommonLayerSyntax NormalForm SourceTermGraph SourceRows
open SourceTermGraphSupportProof SourceTermGraphSemanticProof SourceTermGraphExistentialProof

theorem bindAll_matrix_eval (xs : List Nat) (p : NormalForm.Formula) (ν : Nat → Nat) :
    (bindAll xs (.matrix p)).eval ν ↔ existsPrefix ν xs p := by
  induction xs generalizing ν with
  | nil => rfl
  | cons i xs ih =>
      change (∃ n : Nat, (bindAll xs (.matrix p)).eval (Function.update ν i n)) ↔
        ∃ n : Nat, existsPrefix (Function.update ν i n) xs p
      exact exists_congr (fun n => ih (Function.update ν i n))

/-- Strict natural comparison uses the exact integer row y-x-1, with no
truncated subtraction in its signed meaning. -/
theorem relation_eval (strict : Bool) (x y : Nat) (ν : Nat → Nat) :
    (relation strict x y).eval ν ↔ if strict then ν x < ν y else ν x = ν y := by
  cases strict with
  | false =>
      simp only [relation, Bool.false_eq_true, ↓reduceIte]
      exact variable_equation x y ν
  | true =>
      simp only [relation, ↓reduceIte, NormalForm.Formula.eval, NormalForm.Atom.eval,
        strictRow, rowValue, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        Summand.term, Term.value, one_mul, neg_one_mul, add_zero]
      omega

/-- Both output names denote their actual source values under one shared
original valuation, even when the source operands repeat the same variables. -/
theorem graph_operand_values (start : Nat) (a b : BaseTerm) (ν σ : Nat → Nat)
    (hf : Fresh start (.add a b))
    (hframe : ∀ i, i ∉ allocated start (.add a b) → σ i = ν i)
    (hgraph : (graph start (.add a b)).eval σ) :
    σ (output start a) = a.value ν ∧
      σ (output (start + nodeCount a) b) = b.value ν := by
  have hsource : ∀ i ∈ (BaseTerm.add a b).variables, σ i = ν i := by
    intro i hi
    apply hframe i
    intro hnode
    have hlow := hf i hi
    have hrange := (mem_allocated start (.add a b) i).mp hnode
    omega
  have ha : a.value σ = a.value ν := source_value_congr a σ ν
    (fun i hi => hsource i (List.mem_append_left _ hi))
  have hb : b.value σ = b.value ν := source_value_congr b σ ν
    (fun i hi => hsource i (List.mem_append_right _ hi))
  obtain ⟨hga, hgb, _⟩ := (graph_add start a b σ).mp hgraph
  exact ⟨(graphSoundness start a σ hga).trans ha,
    (graphSoundness (start + nodeCount a) b σ hgb).trans hb⟩

theorem exactLocalAtomIntroduction : SourceRowsTargets.ExactLocalAtomIntroduction := by
  intro strict a b ν
  have hf := SourceRowsSupportProof.localStart_fresh a b
  unfold localAtom
  rw [bindAll_matrix_eval, existsPrefix_iff_frame]
  constructor
  · rintro ⟨σ, hframe, hbody⟩
    change (graph (localStart a b) (.add a b)).eval σ ∧
      (relation strict (output (localStart a b) a)
        (output (localStart a b + nodeCount a) b)).eval σ at hbody
    obtain ⟨ha, hb⟩ := graph_operand_values (localStart a b) a b ν σ hf hframe hbody.1
    have hr := (relation_eval strict (output (localStart a b) a)
      (output (localStart a b + nodeCount a) b) σ).mp hbody.2
    simpa only [ha, hb] using hr
  · intro hsource
    obtain ⟨σ, hframe, hgraph, _⟩ := totalGraphRealization (localStart a b) (.add a b) ν hf
    obtain ⟨ha, hb⟩ := graph_operand_values (localStart a b) a b ν σ hf hframe hgraph
    refine ⟨σ, hframe, ?_⟩
    change (graph (localStart a b) (.add a b)).eval σ ∧
      (relation strict (output (localStart a b) a)
        (output (localStart a b + nodeCount a) b)).eval σ
    refine ⟨hgraph, (relation_eval strict (output (localStart a b) a)
      (output (localStart a b + nodeCount a) b) σ).mpr ?_⟩
    simpa only [ha, hb] using hsource

theorem exactSourceIntroduction : SourceRowsTargets.ExactSourceIntroduction := by
  intro p
  induction p with
  | equal a b =>
      intro ν
      simpa only [SourceRows.translate, SourceFormula.eval, Bool.false_eq_true,
        ↓reduceIte] using exactLocalAtomIntroduction false a b ν
  | less a b =>
      intro ν
      simpa only [SourceRows.translate, SourceFormula.eval, ↓reduceIte] using
        exactLocalAtomIntroduction true a b ν
  | negative p ih =>
      intro ν
      exact not_congr (ih ν)
  | conjunction p q ihp ihq =>
      intro ν
      exact and_congr (ihp ν) (ihq ν)
  | existsNat i p ih =>
      intro ν
      exact exists_congr (fun n => ih (Function.update ν i n))

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceRowsSemanticProof
