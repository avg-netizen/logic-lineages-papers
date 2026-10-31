module
public import LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationCotreeTargets
public import LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationComponentsProof
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationCotree.Proof
open RankedParse ForestParseRepresentationComponents

private def complementIso {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G ≃g H) : Gᶜ ≃g Hᶜ where
  toEquiv := f.toEquiv
  map_rel_iff' := by
    intro x y
    change (f x ≠ f y ∧ ¬ H.Adj (f x) (f y)) ↔ (x ≠ y ∧ ¬ G.Adj x y)
    exact and_congr f.injective.ne_iff (not_congr f.map_rel_iff)

private theorem joinConnected (n : Nat) (c : Fin (n + 2) → Cotree) :
    (graph (.node .join n c)).Connected := by
  letI : Nonempty (Leaf (.node .join n c)) := ⟨chosenLeaf _⟩
  refine ⟨?_⟩
  rintro ⟨i, x⟩ ⟨j, y⟩
  by_cases hij : i = j
  · subst j
    obtain ⟨k, hk⟩ := exists_ne i
    let z : Leaf (.node .join n c) := ⟨k, chosenLeaf (c k)⟩
    have hx : (graph (.node .join n c)).Adj ⟨i, x⟩ z := by
      simp [graph, Adj, z, Ne.symm hk]
    have hy : (graph (.node .join n c)).Adj z ⟨i, y⟩ := by
      simp [graph, Adj, z, hk]
    exact hx.reachable.trans hy.reachable
  · have hxy : (graph (.node .join n c)).Adj ⟨i, x⟩ ⟨j, y⟩ := by
      simp [graph, Adj, hij]
    exact hxy.reachable

private theorem unionComplementConnected (n : Nat) (c : Fin (n + 2) → Cotree) :
    (graph (.node .union n c))ᶜ.Connected := by
  letI : Nonempty (Leaf (.node .union n c)) := ⟨chosenLeaf _⟩
  have cross (i j : Fin (n + 2)) (h : i ≠ j) (x : Leaf (c i)) (y : Leaf (c j)) :
      (graph (.node .union n c))ᶜ.Adj ⟨i, x⟩ ⟨j, y⟩ := by
    refine ⟨?_, ?_⟩
    · intro he; exact h (congrArg Sigma.fst he)
    · simp [graph, Adj, h]
  refine ⟨?_⟩
  rintro ⟨i, x⟩ ⟨j, y⟩
  by_cases hij : i = j
  · subst j
    obtain ⟨k, hk⟩ := exists_ne i
    exact (cross i k (Ne.symm hk) x (chosenLeaf (c k))).reachable.trans
      (cross k i hk (chosenLeaf (c k)) y).reachable
  · exact (cross i j hij x y).reachable

private theorem unionDisconnected (n : Nat) (c : Fin (n + 2) → Cotree) :
    ¬ (graph (.node .union n c)).Connected := by
  have edgeIndex : ∀ {x y : Leaf (.node .union n c)},
      (graph (.node .union n c)).Adj x y → x.1 = y.1 := by
    rintro ⟨i, x⟩ ⟨j, y⟩ h
    by_contra hij
    simpa [graph, Adj, hij] using h
  have walkIndex : ∀ {x y}, (graph (.node .union n c)).Walk x y → x.1 = y.1 := by
    intro x y p
    induction p with
    | nil => rfl
    | cons h _ ih => exact (edgeIndex h).trans ih
  intro hc
  obtain ⟨p⟩ := hc ⟨0, chosenLeaf (c 0)⟩ ⟨1, chosenLeaf (c 1)⟩
  have he : (0 : Fin (n + 2)) = 1 := walkIndex p
  exact zero_ne_one he

private def fiberIso (o : Operation) (n : Nat) (c : Fin (n + 2) → Cotree)
    (i : Fin (n + 2)) :
    fiberGraph (graph (.node o n c)) Sigma.fst i ≃g graph (c i) where
  toEquiv := Equiv.sigmaSubtype i
  map_rel_iff' := by
    rintro ⟨⟨j, x⟩, hx⟩ ⟨⟨k, y⟩, hy⟩
    change j = i at hx
    change k = i at hy
    subst j
    subst k
    change Adj (c i) x y ↔ Adj (.node o n c) ⟨i, x⟩ ⟨i, y⟩
    simp [Adj]

private def complementFiberIso (o : Operation) (n : Nat) (c : Fin (n + 2) → Cotree)
    (i : Fin (n + 2)) :
    fiberGraph (graph (.node o n c))ᶜ Sigma.fst i ≃g (graph (c i))ᶜ where
  toEquiv := Equiv.sigmaSubtype i
  map_rel_iff' := by
    rintro ⟨⟨j, x⟩, hx⟩ ⟨⟨k, y⟩, hy⟩
    change j = i at hx
    change k = i at hy
    subst j
    subst k
    change (x ≠ y ∧ ¬ Adj (c i) x y) ↔
      ((Sigma.mk i x : Leaf (.node o n c)) ≠ Sigma.mk i y ∧
        ¬ Adj (.node o n c) ⟨i, x⟩ ⟨i, y⟩)
    simp [Adj]

private theorem atomConnected : (graph .atom).Connected := by
  letI : Nonempty (Leaf Cotree.atom) := ⟨()⟩
  refine ⟨?_⟩
  intro x y
  cases x
  cases y
  exact SimpleGraph.Reachable.rfl

private theorem atomComplementConnected : (graph .atom)ᶜ.Connected := by
  letI : Nonempty (Leaf Cotree.atom) := ⟨()⟩
  refine ⟨?_⟩
  intro x y
  cases x
  cases y
  exact SimpleGraph.Reachable.rfl

theorem reducedComponents : Targets.ReducedComponents := by
  intro n c
  constructor
  · intro hc
    refine ⟨fun i => ⟨⟨i, chosenLeaf (c i)⟩, rfl⟩, ?_, ?_⟩
    · intro i
      have hchild : (graph (c i)).Connected := by
        have hroot := (hc i).2
        cases he : c i with
        | atom => exact atomConnected
        | node o m d =>
          cases o with
          | union => simp [he, root] at hroot
          | join => exact joinConnected m d
      exact (fiberIso .union n c i).connected_iff.mpr hchild
    · rintro ⟨i, x⟩ ⟨j, y⟩ h
      by_contra hij
      simpa [graph, Adj, hij] using h
  · intro hc
    refine ⟨fun i => ⟨⟨i, chosenLeaf (c i)⟩, rfl⟩, ?_, ?_⟩
    · intro i
      have hchild : (graph (c i))ᶜ.Connected := by
        have hroot := (hc i).2
        cases he : c i with
        | atom => exact atomComplementConnected
        | node o m d =>
          cases o with
          | union => exact unionComplementConnected m d
          | join => simp [he, root] at hroot
      exact (complementFiberIso .join n c i).connected_iff.mpr hchild
    · rintro ⟨i, x⟩ ⟨j, y⟩ h
      by_contra hij
      have ha : (graph (.node .join n c)).Adj ⟨i, x⟩ ⟨j, y⟩ := by
        simp [graph, Adj, hij]
      exact h.2 ha

private theorem noAtomNodeIso (o : Operation) (n : Nat) (c : Fin (n + 2) → Cotree) :
    ¬ Nonempty (graph .atom ≃g graph (.node o n c)) := by
  rintro ⟨e⟩
  let x : Leaf (.node o n c) := ⟨0, chosenLeaf (c 0)⟩
  let y : Leaf (.node o n c) := ⟨1, chosenLeaf (c 1)⟩
  have he : e.symm x = e.symm y := @Subsingleton.elim Unit _ _ _
  have hi : (0 : Fin (n + 2)) = 1 := congrArg Sigma.fst (e.symm.injective he)
  exact zero_ne_one hi

theorem reducedUniqueness : Targets.ReducedUniqueness := by
  intro s
  induction s with
  | atom =>
    intro t hs ht h
    cases t with
    | atom => exact StructuralIso.atom
    | node o n c => exact False.elim (noAtomNodeIso o n c h)
  | node o n c ih =>
    intro t hs ht h
    obtain ⟨f⟩ := h
    cases t with
    | atom => exact False.elim (noAtomNodeIso o n c ⟨f.symm⟩)
    | node p m d =>
      cases o with
      | union => cases p with
        | join =>
          exact False.elim (unionDisconnected n c (f.connected_iff.mpr (joinConnected m d)))
        | union =>
          obtain ⟨e, _, q⟩ := ForestParseRepresentationComponents.Proof.fiberIsoRecovery
            _ _ _ _ _ _ Sigma.fst Sigma.fst ((reducedComponents n c).1 hs)
            ((reducedComponents m d).1 ht) f
          apply StructuralIso.node e
          intro i
          obtain ⟨q⟩ := q i
          exact ih i (d (e i)) (hs i).1 (ht (e i)).1
            ⟨(fiberIso .union n c i).symm.trans (q.trans (fiberIso .union m d (e i)))⟩
      | join => cases p with
        | union =>
          exact False.elim (unionDisconnected m d (f.connected_iff.mp (joinConnected n c)))
        | join =>
          obtain ⟨e, _, q⟩ := ForestParseRepresentationComponents.Proof.fiberIsoRecovery
            _ _ _ _ _ _ Sigma.fst Sigma.fst ((reducedComponents n c).2 hs)
            ((reducedComponents m d).2 ht) (complementIso f)
          apply StructuralIso.node e
          intro i
          obtain ⟨q⟩ := q i
          have eqc : (graph (c i))ᶜ ≃g (graph (d (e i)))ᶜ :=
            (complementFiberIso .join n c i).symm.trans
              (q.trans (complementFiberIso .join m d (e i)))
          have eqg : graph (c i) ≃g graph (d (e i)) := by
            simpa only [compl_compl] using complementIso eqc
          exact ih i (d (e i)) (hs i).1 (ht (e i)).1 ⟨eqg⟩

end LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationCotree.Proof
