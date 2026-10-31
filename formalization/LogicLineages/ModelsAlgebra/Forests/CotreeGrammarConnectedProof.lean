module
public import LogicLineages.ModelsAlgebra.Forests.CotreeGrammarConnectedTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreeGrammarConnected.Proof
open CotreeGrammar CotreeGrammarFlow CotreeGrammarFlow.Proof

variable {Q : Type} [Fintype Q] [DecidableEq Q]

theorem edge_mono (δ : Q → Q → Q) {a b : Counts Q}
    (hab : ∀ p, a.binary p ≤ b.binary p) {x y} (h : UsedEdge δ a x y) : UsedEdge δ b x y := by
  rcases h with ⟨r,s,hp,he,hy⟩
  exact ⟨r,s,lt_of_lt_of_le hp (hab _),he,hy⟩

theorem path_mono (δ : Q → Q → Q) {a b : Counts Q}
    (hab : ∀ p, a.binary p ≤ b.binary p) {x y}
    (h : Relation.ReflTransGen (UsedEdge δ a) x y) :
    Relation.ReflTransGen (UsedEdge δ b) x y :=
  Relation.ReflTransGen.mono (fun _ _ => edge_mono δ hab) h

theorem leaf_connected (δ : Q → Q → Q) (B : Finset Q) (q : Q) :
    Connected δ q (leafCounts B q) := by
  intro r hr
  by_cases he : r = q
  · subst r; exact .refl
  · have hz : consumed δ (leafCounts B q) r = 0 := by
      simp [consumed, leafCounts, Prod.mk.injEq, he]
    omega

theorem node_connected (δ : Q → Q → Q) (r s : Q) {a b : Counts Q}
    (ha : Connected δ r a) (hb : Connected δ s b) :
    Connected δ (δ r s) (nodeCounts r s a b) := by
  have hla : ∀ p, a.binary p ≤ (nodeCounts r s a b).binary p := by
    intro p; simp only [nodeCounts]; omega
  have hlb : ∀ p, b.binary p ≤ (nodeCounts r s a b).binary p := by
    intro p; simp only [nodeCounts]; omega
  have hpos : 0 < (nodeCounts r s a b).binary (r,s) := by
    simp only [nodeCounts, if_pos rfl, if_true]; omega
  have leftEdge : UsedEdge δ (nodeCounts r s a b) (δ r s) r :=
    ⟨r,s,hpos,rfl,Or.inl rfl⟩
  have rightEdge : UsedEdge δ (nodeCounts r s a b) (δ r s) s :=
    ⟨r,s,hpos,rfl,Or.inr rfl⟩
  intro q hq
  rw [node_consumed] at hq
  by_cases he : δ r s = q
  · subst q; exact .refl
  · simp only [if_neg he, Nat.add_zero] at hq
    have hh : 0 < consumed δ a q ∨ 0 < consumed δ b q := by omega
    rcases hh with hl | hr
    · exact (Relation.ReflTransGen.single leftEdge).trans (path_mono δ hla (ha q hl))
    · exact (Relation.ReflTransGen.single rightEdge).trans (path_mono δ hlb (hb q hr))

theorem connectedFlowNecessary : Targets.ConnectedFlowNecessary := by
  intro Q _ _ δ q w h
  have ht := (CotreeGrammar.StatementChecks.grammarLanguageExact Q δ q w).mp h
  clear h
  induction ht with
  | leaf B q hq => exact ⟨leafCounts B q, leaf_realizes δ B q hq, leaf_connected δ B q⟩
  | node _ _ ihl ihr =>
    rcases ihl with ⟨a,ha,hac⟩
    rcases ihr with ⟨b,hb,hbc⟩
    exact ⟨_,node_realizes δ ha hb,node_connected δ _ _ hac hbc⟩

end LogicLineages.ModelsAlgebra.Forests.CotreeGrammarConnected.Proof
