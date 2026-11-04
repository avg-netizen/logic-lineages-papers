module
public import LogicLineages.OrdinalComparison.ParametricFinitePairCollapseRepresentationProof
public import LogicLineages.OrdinalComparison.ParametricActualCollapseRecursionProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricFinitePairCollapse.Proof

theorem predecessor_test (G : Nat → Nat) (p q : Nat × Nat) :
    q ∈ predecessors G p ↔ Below q p ∧ pairNorm q ≤ G (pairNorm p) := by
  rw [predecessors,Finset.mem_filter]
  change (q ∈ (Finset.range (p.1+1)).product (Finset.range (G (pairNorm p)+1)) ∧
    (Below q p ∧ pairNorm q ≤ G (pairNorm p))) ↔ _
  constructor
  · exact fun h => h.2
  · intro h
    have hq : q.1≤p.1 := by rcases h.1 with hlt | ⟨he,_⟩ <;> omega
    have hr : q.2≤G (pairNorm p) := by have hh := h.2; change 2*q.1+q.2≤G (pairNorm p) at hh; omega
    exact ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),
      Finset.mem_range.mpr (by omega)⟩,h⟩

theorem bounded_mem (p : Nat × Nat) (B : Nat) (x : Ordinal) :
    x ∈ actualBoundedPredecessors (ordinal p) B ↔
      x<ordinal p ∧ actualOrdinalNorm x≤B := by
  classical
  have hp := (exactRepresentation.1 p).1
  simp only [actualBoundedPredecessors,Finset.mem_filter,Set.Finite.mem_toFinset,Set.mem_setOf_eq]
  exact ⟨fun h => ⟨h.2,h.1.2⟩,fun h => ⟨⟨h.1.trans hp,h.2⟩,h.1⟩⟩

theorem exactPredecessors : Targets.ExactPredecessors := by
  intro G p x
  rw [bounded_mem,(exactRepresentation.1 p).2]
  constructor
  · rintro ⟨hx,hn⟩
    obtain ⟨q,hq,rfl⟩ := (exactRepresentation.2.2 p x).mp hx
    rw [(exactRepresentation.1 q).2] at hn
    exact ⟨q,(predecessor_test G p q).mpr ⟨hq,hn⟩,rfl⟩
  · rintro ⟨q,hq,rfl⟩
    have h := (predecessor_test G p q).mp hq
    exact ⟨(exactRepresentation.2.2 p (ordinal q)).mpr ⟨q,h.1,rfl⟩,
      by rw [(exactRepresentation.1 q).2]; exact h.2⟩

theorem exactMaximum : Targets.ExactMaximum := by
  intro G p
  have he := ParametricActualCollapse.Proof.equation G (ordinal p) (exactRepresentation.1 p).1
  apply Nat.le_antisymm
  · apply he.2
    intro x hx hn
    have hm := (bounded_mem p (G (actualOrdinalNorm (ordinal p))) x).mpr ⟨hx,hn⟩
    obtain ⟨q,hq,rfl⟩ := (exactPredecessors G p x).mp hm
    exact Finset.le_sup (f:=fun q => value G q+1) hq
  · apply Finset.sup_le
    intro q hq
    have hm := (exactPredecessors G p (ordinal q)).mpr ⟨q,hq,rfl⟩
    have h := (bounded_mem p (G (actualOrdinalNorm (ordinal p))) (ordinal q)).mp hm
    exact he.1 (ordinal q) h.1 h.2
end LogicLineages.OrdinalComparison.Source.ParametricFinitePairCollapse.Proof
