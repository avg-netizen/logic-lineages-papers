module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphFrameProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphSoundnessProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphProof
open ExpandedGraph

/-- Finite postorder composition. Every premise is discharged by the concrete
child graphs in the structural realization proof below. -/
theorem realize_binary (start : Nat) (a b t : Term) (ν : Nat → Nat)
    (hcount : nodeCount t = nodeCount a + nodeCount b + 1)
    (hvars : ∀ i, i ∈ a.variables ∨ i ∈ b.variables → i ∈ t.variables)
    (ha : PlainBlockSplit.termHFree a = true) (hb : PlainBlockSplit.termHFree b = true)
    (hbuild : ∀ σ : Nat → Nat, (graph start a).eval σ →
      (graph (start + nodeCount a) b).eval σ →
      σ (output start t) = t.value σ → (graph start t).eval σ)
    (hrea : ∀ s μ, Fresh s a → ∃ σ : Nat → Nat,
      (∀ i, i ∉ allocated s a → σ i = μ i) ∧ (graph s a).eval σ ∧ σ (output s a) = a.value μ)
    (hreb : ∀ s μ, Fresh s b → ∃ σ : Nat → Nat,
      (∀ i, i ∉ allocated s b → σ i = μ i) ∧ (graph s b).eval σ ∧ σ (output s b) = b.value μ)
    (hf : Fresh start t) : ∃ σ : Nat → Nat,
      (∀ i, i ∉ allocated start t → σ i = ν i) ∧
      (graph start t).eval σ ∧ σ (output start t) = t.value ν := by
  have hfa : Fresh start a := fun i hi => hf i (hvars i (Or.inl hi))
  have hfb : Fresh (start + nodeCount a) b :=
    fresh_mono (by omega) (fun i hi => hf i (hvars i (Or.inr hi)))
  obtain ⟨μ, hframeA, hgraphA, _⟩ := hrea start ν hfa
  obtain ⟨τ, hframeB, hgraphB, _⟩ := hreb (start + nodeCount a) μ hfb
  let z := start + nodeCount a + nodeCount b
  have hz : output start t = z := by unfold output; rw [hcount]; dsimp [z]; omega
  let σ := Function.update τ z (t.value ν)
  have hframe : ∀ i, i ∉ allocated start t → σ i = ν i := by
    intro i hi
    have hna : i ∉ allocated start a := by
      intro hm
      apply hi
      rw [mem_allocated] at hm ⊢
      rw [hcount]
      omega
    have hnb : i ∉ allocated (start + nodeCount a) b := by
      intro hm
      apply hi
      rw [mem_allocated] at hm ⊢
      rw [hcount]
      omega
    have hne : i ≠ z := by
      intro he
      apply hi
      rw [mem_allocated, hcount, he]
      dsimp [z]
      omega
    exact (Function.update_of_ne hne _ _).trans ((hframeB i hnb).trans (hframeA i hna))
  have hgraphAτ := (graph_frame_after start a (start + nodeCount a) b μ τ ha hfa
    (by omega) hframeB).mpr hgraphA
  have hgraphAσ : (graph start a).eval σ :=
    (graph_update_after start a τ z _ ha hfa (by dsimp [z]; omega)).mpr hgraphAτ
  have hgraphBσ : (graph (start + nodeCount a) b).eval σ :=
    (graph_update_after (start + nodeCount a) b τ z _ hb hfb (by dsimp [z]; omega)).mpr hgraphB
  have hσz : σ (output start t) = t.value ν := by rw [hz]; exact Function.update_self _ _ _
  refine ⟨σ, hframe, hbuild σ hgraphAσ hgraphBσ ?_, hσz⟩
  exact hσz.trans (source_frame t t start ν σ hf hframe).symm

theorem realize_unary (start : Nat) (a t : Term) (ν : Nat → Nat)
    (hcount : nodeCount t = nodeCount a + 1)
    (hvars : ∀ i ∈ a.variables, i ∈ t.variables)
    (ha : PlainBlockSplit.termHFree a = true)
    (hbuild : ∀ σ : Nat → Nat, (graph start a).eval σ →
      σ (output start t) = t.value σ → (graph start t).eval σ)
    (hrea : ∀ s μ, Fresh s a → ∃ σ : Nat → Nat,
      (∀ i, i ∉ allocated s a → σ i = μ i) ∧ (graph s a).eval σ ∧ σ (output s a) = a.value μ)
    (hf : Fresh start t) : ∃ σ : Nat → Nat,
      (∀ i, i ∉ allocated start t → σ i = ν i) ∧
      (graph start t).eval σ ∧ σ (output start t) = t.value ν := by
  have hfa : Fresh start a := fun i hi => hf i (hvars i hi)
  obtain ⟨μ, hframeA, hgraphA, _⟩ := hrea start ν hfa
  let z := start + nodeCount a
  have hz : output start t = z := by unfold output; rw [hcount]; dsimp [z]
  let σ := Function.update μ z (t.value ν)
  have hframe : ∀ i, i ∉ allocated start t → σ i = ν i := by
    intro i hi
    have hna : i ∉ allocated start a := by
      intro hm
      apply hi
      rw [mem_allocated] at hm ⊢
      rw [hcount]
      omega
    have hne : i ≠ z := by
      intro he
      apply hi
      rw [mem_allocated, hcount, he]
      dsimp [z]
      omega
    exact (Function.update_of_ne hne _ _).trans (hframeA i hna)
  have hgraphAσ : (graph start a).eval σ :=
    (graph_update_after start a μ z _ ha hfa (by dsimp [z]; exact le_rfl)).mpr hgraphA
  have hσz : σ (output start t) = t.value ν := by rw [hz]; exact Function.update_self _ _ _
  refine ⟨σ, hframe, hbuild σ hgraphAσ ?_, hσz⟩
  exact hσz.trans (source_frame t t start ν σ hf hframe).symm

#print axioms realize_binary
#print axioms realize_unary
end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphProof
