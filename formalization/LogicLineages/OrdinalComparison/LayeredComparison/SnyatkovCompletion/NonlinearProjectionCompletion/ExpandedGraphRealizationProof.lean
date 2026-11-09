module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphRealizationHelpersProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphProof
open ExpandedGraph

theorem totalGraphRealization : ExpandedGraphTargets.TotalGraphRealization := by
  intro start t
  induction t generalizing start with
  | numeral n =>
      intro ν ht hf
      refine ⟨Function.update ν start n, ?_, ?_, ?_⟩
      · intro i hi
        have hne : i ≠ start := by
          intro he
          subst i
          exact hi ((mem_allocated start (.numeral n) start).mpr (by simp [nodeCount]))
        exact Function.update_of_ne hne _ _
      · exact (graph_numeral start n _).mpr (Function.update_self _ _ _)
      · simp only [output, nodeCount, Nat.add_sub_cancel, Function.update_self, Term.value]
  | «variable» j =>
      intro ν ht hf
      have hj : j < start := hf j (List.mem_singleton_self _)
      refine ⟨Function.update ν start (ν j), ?_, ?_, ?_⟩
      · intro i hi
        have hne : i ≠ start := by
          intro he
          subst i
          exact hi ((mem_allocated start (.variable j) start).mpr (by simp [nodeCount]))
        exact Function.update_of_ne hne _ _
      · apply (graph_variable start j _).mpr
        simp only [Function.update_self, Function.update_of_ne (Nat.ne_of_lt hj)]
      · simp only [output, nodeCount, Nat.add_sub_cancel, Function.update_self, Term.value]
  | add a b iha ihb =>
      intro ν ht hf
      have ha := (Bool.and_eq_true_iff.mp ht).1
      have hb := (Bool.and_eq_true_iff.mp ht).2
      apply realize_binary start a b (.add a b) ν rfl
        (fun i hi => List.mem_append.mpr hi) ha hb ?_
        (fun s μ h => iha s μ ha h) (fun s μ h => ihb s μ hb h) hf
      intro σ hga hgb hv
      apply (graph_add start a b σ).mpr
      refine ⟨hga, hgb, ?_⟩
      rw [graphSoundness start a σ ha hga, graphSoundness (start + nodeCount a) b σ hb hgb]
      exact hv
  | subtract a b iha ihb =>
      intro ν ht hf
      have ha := (Bool.and_eq_true_iff.mp ht).1
      have hb := (Bool.and_eq_true_iff.mp ht).2
      apply realize_binary start a b (.subtract a b) ν rfl
        (fun i hi => List.mem_append.mpr hi) ha hb ?_
        (fun s μ h => iha s μ ha h) (fun s μ h => ihb s μ hb h) hf
      intro σ hga hgb hv
      apply (graph_subtract start a b σ).mpr
      refine ⟨hga, hgb, ?_⟩
      rw [graphSoundness start a σ ha hga, graphSoundness (start + nodeCount a) b σ hb hgb]
      exact hv
  | multiply c a ih =>
      intro ν ht hf
      apply realize_unary start a (.multiply c a) ν rfl (fun i hi => hi) ht ?_
        (fun s μ h => ih s μ ht h) hf
      intro σ hga hv
      apply (graph_multiply start c a σ).mpr
      refine ⟨hga, ?_⟩
      rw [graphSoundness start a σ ht hga]
      exact hv
  | divide c a ih =>
      intro ν ht hf
      apply realize_unary start a (.divide c a) ν rfl (fun i hi => hi) ht ?_
        (fun s μ h => ih s μ ht h) hf
      intro σ hga hv
      apply (graph_divide start c a σ).mpr
      refine ⟨hga, ?_⟩
      rw [graphSoundness start a σ ht hga]
      exact hv
  | phi a ih =>
      intro ν ht hf
      apply realize_unary start a (.phi a) ν rfl (fun i hi => hi) ht ?_
        (fun s μ h => ih s μ ht h) hf
      intro σ hga hv
      apply (graph_phi start a σ).mpr
      refine ⟨hga, ?_⟩
      rw [graphSoundness start a σ ht hga]
      exact hv
  | phiInverse a ih =>
      intro ν ht hf
      have hfa : Fresh start a := hf
      obtain ⟨μ, hframeA, hgraphA, _⟩ := ih start ν ht hfa
      let u := start + nodeCount a
      let z := u + 1
      let v := (Term.phiInverse a).value ν
      have hz : output start (.phiInverse a) = z := by
        simp only [output, nodeCount]
        dsimp [z, u]
        omega
      let τ := Function.update μ u (v + 1)
      let σ := Function.update τ z v
      have huz : u ≠ z := by dsimp [z]; omega
      have hframe : ∀ i, i ∉ allocated start (.phiInverse a) → σ i = ν i := by
        intro i hi
        have hna : i ∉ allocated start a := by
          intro hm
          apply hi
          rw [mem_allocated] at hm ⊢
          simp only [nodeCount]
          omega
        have hnu : i ≠ u := by
          intro he
          apply hi
          rw [mem_allocated, he]
          simp only [nodeCount]
          dsimp [u]
          omega
        have hnz : i ≠ z := by
          intro he
          apply hi
          rw [mem_allocated, he]
          simp only [nodeCount]
          dsimp [z, u]
          omega
        calc
          σ i = τ i := Function.update_of_ne hnz _ _
          _ = μ i := Function.update_of_ne hnu _ _
          _ = ν i := hframeA i hna
      have hgraphAτ : (graph start a).eval τ :=
        (graph_update_after start a μ u _ ht hfa (by dsimp [u]; exact le_rfl)).mpr hgraphA
      have hgraphAσ : (graph start a).eval σ :=
        (graph_update_after start a τ z _ ht hfa (by dsimp [z, u]; omega)).mpr hgraphAτ
      have hσz : σ z = v := Function.update_self _ _ _
      have hσu : σ u = v + 1 := by
        dsimp [σ, τ]
        rw [Function.update_of_ne huz, Function.update_self]
      refine ⟨σ, hframe, (graph_phiInverse start a σ).mpr ⟨hgraphAσ, ?_, ?_⟩, ?_⟩
      · rw [hz]
        exact hσu.trans (congrArg (· + 1) hσz.symm)
      · rw [hz, hσz, graphSoundness start a σ ht hgraphAσ]
        exact (source_frame (.phiInverse a) (.phiInverse a) start ν σ hf hframe).symm
      · rw [hz]
        exact hσz
  | hyper a ih => intro ν ht; simp only [PlainBlockSplit.termHFree, Bool.false_eq_true] at ht
  | hyperInverse a ih => intro ν ht; simp only [PlainBlockSplit.termHFree, Bool.false_eq_true] at ht

#print axioms totalGraphRealization
end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphProof
