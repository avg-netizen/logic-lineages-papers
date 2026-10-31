module
public import LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationACTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationAC.Proof
open RankedParse

private def swapIso (o : Operation) (s t : Term) :
    graph (.node o s t) ≃g graph (.node o t s) where
  toEquiv := Equiv.sumComm (Leaf s) (Leaf t)
  map_rel_iff' := by
    intro x y
    cases x <;> cases y <;> rfl

private def assocIso (o : Operation) (r s t : Term) :
    graph (.node o (.node o r s) t) ≃g graph (.node o r (.node o s t)) where
  toEquiv := Equiv.sumAssoc (Leaf r) (Leaf s) (Leaf t)
  map_rel_iff' := by
    intro x y
    rcases x with (x | x) | x <;> rcases y with (y | y) | y <;> rfl

private def congrIso (o : Operation) {s s' t t' : Term}
    (f : graph s ≃g graph s') (g : graph t ≃g graph t') :
    graph (.node o s t) ≃g graph (.node o s' t') where
  toEquiv := Equiv.sumCongr f.toEquiv g.toEquiv
  map_rel_iff' := by
    intro x y
    cases x with
    | inl x => cases y with
      | inl y => exact f.map_rel_iff
      | inr y => rfl
    | inr x => cases y with
      | inl y => rfl
      | inr y => exact g.map_rel_iff

theorem graphAssociationSound : Targets.GraphAssociationSound := by
  intro s t h
  induction h with
  | refl t => exact ⟨SimpleGraph.Iso.refl⟩
  | symm _ ih => obtain ⟨e⟩ := ih; exact ⟨e.symm⟩
  | trans _ _ ih₁ ih₂ => obtain ⟨e⟩ := ih₁; obtain ⟨f⟩ := ih₂; exact ⟨e.trans f⟩
  | congr o _ _ ih₁ ih₂ =>
    obtain ⟨e⟩ := ih₁; obtain ⟨f⟩ := ih₂
    exact ⟨congrIso o e f⟩
  | swap o s t => exact ⟨swapIso o s t⟩
  | assoc o r s t => exact ⟨assocIso o r s t⟩

private theorem crossConnected {α β : Type} (a : α) (b : β)
    (G : SimpleGraph (Sum α β))
    (h : ∀ x y, G.Adj (.inl x) (.inr y)) : G.Connected := by
  letI : Nonempty (Sum α β) := ⟨.inl a⟩
  refine ⟨?_⟩
  intro x y
  cases x with
  | inl x => cases y with
    | inl y => exact (h x b).reachable.trans (h y b).reachable.symm
    | inr y => exact (h x y).reachable
  | inr x => cases y with
    | inl y => exact (h y x).reachable.symm
    | inr y => exact (h a x).reachable.symm.trans (h a y).reachable

private theorem noCrossDisconnected {α β : Type} (a : α) (b : β)
    (G : SimpleGraph (Sum α β))
    (h : ∀ x y, ¬ G.Adj (.inl x) (.inr y)) : ¬ G.Connected := by
  let side : Sum α β → Bool := Sum.elim (fun _ => false) (fun _ => true)
  have edgeSide : ∀ {x y}, G.Adj x y → side x = side y := by
    intro x y hxy
    cases x with
    | inl x => cases y with
      | inl y => rfl
      | inr y => exact False.elim (h x y hxy)
    | inr x => cases y with
      | inl y => exact False.elim (h y x (G.adj_symm hxy))
      | inr y => rfl
  have walkSide : ∀ {x y}, G.Walk x y → side x = side y := by
    intro x y p
    induction p with
    | nil => rfl
    | cons hxy _ ih => exact (edgeSide hxy).trans ih
  intro hc
  obtain ⟨p⟩ := hc (.inl a) (.inr b)
  exact Bool.false_ne_true (walkSide p)

theorem rootConnectivity : Targets.RootConnectivity := by
  intro s t
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply noCrossDisconnected (chosenLeaf s) (chosenLeaf t)
    intro x y
    change ¬ Operation.union = Operation.join
    intro h; cases h
  · apply crossConnected (chosenLeaf s) (chosenLeaf t)
    intro x y
    change Operation.join = Operation.join
    rfl
  · apply crossConnected (chosenLeaf s) (chosenLeaf t)
    intro x y
    simp [SimpleGraph.compl_adj, graph, Adj]
  · apply noCrossDisconnected (chosenLeaf s) (chosenLeaf t)
    intro x y
    simp [SimpleGraph.compl_adj, graph, Adj]

end LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationAC.Proof
