module

public import LogicLineages.ModelsAlgebra.Forests.GraphUniversalTargets
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic.FinCases

/-! External continuation: the actual graph-theoretic universal-vertex supplier
for paper 03. The four-vertex obstruction is an induced relation embedding,
not an adjacency-only graph homomorphism. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.GraphUniversalProof

open GraphBridge

private theorem four_pattern {α : Type} (G : SimpleGraph α) (a b c d : α)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d)
    (hac : ¬ G.Adj a c) (hbd : ¬ G.Adj b d)
    (hacne : a ≠ c) (hbdne : b ≠ d) (hadne : a ≠ d) :
    Nonempty (fourPath ↪g G) ∨ Nonempty (fourCycle ↪g G) := by
  classical
  have hba := G.adj_symm hab
  have hcb := G.adj_symm hbc
  have hdc := G.adj_symm hcd
  have hca : ¬ G.Adj c a := fun h => hac (G.adj_symm h)
  have hdb : ¬ G.Adj d b := fun h => hbd (G.adj_symm h)
  have habne := G.ne_of_adj hab
  have hbcne := G.ne_of_adj hbc
  have hcdne := G.ne_of_adj hcd
  let f : Fin 4 → α := fun i => if i = 0 then a else if i = 1 then b else if i = 2 then c else d
  have hi : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f]
  by_cases had : G.Adj a d
  · have hda := G.adj_symm had
    right
    refine ⟨⟨⟨f, hi⟩, ?_⟩⟩
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [f, fourCycle, SimpleGraph.fromRel_adj, hab, hba, hbc, hcb,
        hcd, hdc, hac, hca, hbd, hdb, had, hda]
  · have hda : ¬ G.Adj d a := fun h => had (G.adj_symm h)
    left
    refine ⟨⟨⟨f, hi⟩, ?_⟩⟩
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [f, fourPath, SimpleGraph.fromRel_adj, hab, hba, hbc, hcb,
        hcd, hdc, hac, hca, hbd, hdb, had, hda]

theorem adjacentClosedNeighborhoodsNested : Targets.AdjacentClosedNeighborhoodsNested := by
  classical
  intro α _ G hp hc v w hvw
  by_contra hn
  have hn₁ : ¬ closedNeighborhood G v ⊆ closedNeighborhood G w :=
    fun h => hn (Or.inl h)
  have hn₂ : ¬ closedNeighborhood G w ⊆ closedNeighborhood G v :=
    fun h => hn (Or.inr h)
  obtain ⟨u, huv, huw⟩ := Set.not_subset.mp hn₁
  obtain ⟨x, hxw, hxv⟩ := Set.not_subset.mp hn₂
  change u = v ∨ G.Adj v u at huv
  change ¬ (u = w ∨ G.Adj w u) at huw
  change x = w ∨ G.Adj w x at hxw
  change ¬ (x = v ∨ G.Adj v x) at hxv
  have hu_ne_w : u ≠ w := fun h => huw (Or.inl h)
  have hx_ne_v : x ≠ v := fun h => hxv (Or.inl h)
  have hnwu : ¬ G.Adj w u := fun h => huw (Or.inr h)
  have hnvx : ¬ G.Adj v x := fun h => hxv (Or.inr h)
  have hvu : G.Adj v u := huv.resolve_left (by
    intro h; subst u; exact hnwu (G.adj_symm hvw))
  have hwx : G.Adj w x := hxw.resolve_left (by
    intro h; subst x; exact hnvx hvw)
  have hu_ne_x : u ≠ x := by
    intro h; subst x; exact hnvx hvu
  rcases four_pattern G u v w x (G.adj_symm hvu) hvw hwx
      (fun h => hnwu (G.adj_symm h)) hnvx hu_ne_w hx_ne_v.symm hu_ne_x with h | h
  · exact hp h
  · exact hc h

theorem connectedForbiddenHasUniversalVertex : Targets.ConnectedForbiddenHasUniversalVertex := by
  classical
  intro α _ G hp hc hconn
  letI : Nonempty α := hconn.nonempty
  let N (v : α) : Finset α := Finset.univ.filter (fun x => x ∈ closedNeighborhood G v)
  have memN (v x : α) : x ∈ N v ↔ x ∈ closedNeighborhood G v := by simp [N]
  obtain ⟨v, _, hv⟩ := Finset.exists_max_image Finset.univ (fun w => (N w).card)
    (Finset.univ_nonempty : (Finset.univ : Finset α).Nonempty)
  have contained (w : α) (hw : w ∈ closedNeighborhood G v) :
      closedNeighborhood G w ⊆ closedNeighborhood G v := by
    rcases hw with rfl | hvw
    · exact Set.Subset.refl _
    rcases adjacentClosedNeighborhoodsNested α G hp hc v w hvw with h | h
    · have hfin : N v ⊆ N w := by
        intro x hx; exact (memN w x).mpr (h ((memN v x).mp hx))
      have heq := Finset.eq_of_subset_of_card_le hfin (hv w (Finset.mem_univ w))
      intro x hx
      exact (memN v x).mp (heq ▸ (memN w x).mpr hx)
    · exact h
  have walks {a b : α} (p : G.Walk a b) :
      a ∈ closedNeighborhood G v → b ∈ closedNeighborhood G v := by
    induction p with
    | nil => exact id
    | @cons a b c hab p ih =>
      intro ha
      exact ih (contained a ha (Or.inr hab))
  refine ⟨v, fun w hw => ?_⟩
  obtain ⟨p⟩ := hconn v w
  exact (walks p (Or.inl rfl)).resolve_left hw

end LogicLineages.ModelsAlgebra.Forests.GraphUniversalProof
