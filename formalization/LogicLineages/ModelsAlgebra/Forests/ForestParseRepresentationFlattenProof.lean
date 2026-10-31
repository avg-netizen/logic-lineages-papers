module
public import LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationFlattenTargets
public import LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationCotreeProof
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationFlatten.Proof
open RankedParse ForestParseRepresentationCotree

noncomputable def familyIso {I J : Type} (o : Operation) (c : I → Cotree) (d : J → Cotree)
    (e : I ≃ J) (f : ∀ i, ForestParseRepresentationCotree.graph (c i) ≃g
      ForestParseRepresentationCotree.graph (d (e i))) : familyGraph o c ≃g familyGraph o d where
  toEquiv := Equiv.sigmaCongr e (fun i => (f i).toEquiv)
  map_rel_iff' := by
    rintro ⟨i, x⟩ ⟨j, y⟩
    change familyAdj o d ⟨e i, f i x⟩ ⟨e j, f j y⟩ ↔ familyAdj o c ⟨i, x⟩ ⟨j, y⟩
    by_cases hij : i = j
    · subst j
      simpa [familyAdj, ForestParseRepresentationCotree.graph] using (f i).map_rel_iff (a := x) (b := y)
    · simp [familyAdj, hij, e.injective.ne_iff.mpr hij]

noncomputable def nodeFamilyIso (o : Operation) (n : Nat)
    (c : Fin (n + 2) → Cotree) :
    ForestParseRepresentationCotree.graph (.node o n c) ≃g familyGraph o c where
  toEquiv := Equiv.refl _
  map_rel_iff' := by
    rintro ⟨i, x⟩ ⟨j, y⟩
    change familyAdj o c ⟨i, x⟩ ⟨j, y⟩ ↔ ForestParseRepresentationCotree.Adj (.node o n c) ⟨i, x⟩ ⟨j, y⟩
    by_cases hij : i = j
    · subst j; simp [familyAdj, ForestParseRepresentationCotree.Adj]
    · simp [familyAdj, ForestParseRepresentationCotree.Adj, hij]

noncomputable def singletonIso (o : Operation) (t : Cotree) :
    ForestParseRepresentationCotree.graph t ≃g familyGraph o (singletonFamily t).child where
  toEquiv := (Equiv.uniqueSigma (fun _ : Fin 1 => ForestParseRepresentationCotree.Leaf t)).symm
  map_rel_iff' := by
    intro x y
    change familyAdj o (fun _ : Fin 1 => t) ⟨0, x⟩ ⟨0, y⟩ ↔
      ForestParseRepresentationCotree.Adj t x y
    simp [familyAdj]

noncomputable def frontierIso (o : Operation) (t : Cotree) :
    ForestParseRepresentationCotree.graph t ≃g familyGraph o (frontier o t).child := by
  cases t with
  | atom => exact singletonIso o .atom
  | node p n c =>
    by_cases hp : p = o
    · subst p
      rw [show frontier o (.node o n c) = ⟨n + 2, Nat.zero_lt_succ _, c⟩ by simp [frontier]]
      exact nodeFamilyIso o n c
    · rw [show frontier o (.node p n c) = singletonFamily (.node p n c) by simp [frontier, hp]]
      exact singletonIso o (.node p n c)

def operationIso {V W V' W' : Type} (o : Operation)
    {G : SimpleGraph V} {H : SimpleGraph W} {G' : SimpleGraph V'} {H' : SimpleGraph W'}
    (f : G ≃g G') (g : H ≃g H') : operationGraph o G H ≃g operationGraph o G' H' where
  toEquiv := Equiv.sumCongr f.toEquiv g.toEquiv
  map_rel_iff' := by
    rintro (x | x) (y | y)
    · exact f.map_rel_iff
    · rfl
    · rfl
    · exact g.map_rel_iff

noncomputable def sumFamilyIso {I J : Type} (o : Operation) (c : I → Cotree) (d : J → Cotree) :
    operationGraph o (familyGraph o c) (familyGraph o d) ≃g familyGraph o (Sum.elim c d) where
  toEquiv := (Equiv.sumSigmaDistrib (fun z : Sum I J =>
    ForestParseRepresentationCotree.Leaf (Sum.elim c d z))).symm
  map_rel_iff' := by
    rintro (⟨i, x⟩ | ⟨i, x⟩) (⟨j, y⟩ | ⟨j, y⟩)
    · change familyAdj o (Sum.elim c d) ⟨.inl i, x⟩ ⟨.inl j, y⟩ ↔ familyAdj o c ⟨i, x⟩ ⟨j, y⟩
      by_cases h : i = j
      · subst j; simp [familyAdj]
      · simp [familyAdj, h]
    · change familyAdj o (Sum.elim c d) ⟨.inl i, x⟩ ⟨.inr j, y⟩ ↔ o = .join
      simp [familyAdj]
    · change familyAdj o (Sum.elim c d) ⟨.inr i, x⟩ ⟨.inl j, y⟩ ↔ o = .join
      simp [familyAdj]
    · change familyAdj o (Sum.elim c d) ⟨.inr i, x⟩ ⟨.inr j, y⟩ ↔ familyAdj o d ⟨i, x⟩ ⟨j, y⟩
      by_cases h : i = j
      · subst j; simp [familyAdj]
      · simp [familyAdj, h]

noncomputable def concatenateIso (o : Operation) (f g : Family) :
    operationGraph o (familyGraph o f.child) (familyGraph o g.child) ≃g
      familyGraph o (concatenate f g).child := by
  let e : Sum (Fin f.count) (Fin g.count) ≃ Fin (f.count + g.count) := finSumFinEquiv
  have hf : ∀ i, ForestParseRepresentationCotree.graph (Sum.elim f.child g.child i) ≃g
      ForestParseRepresentationCotree.graph ((concatenate f g).child (e i)) := by
    intro i
    change ForestParseRepresentationCotree.graph (Sum.elim f.child g.child i) ≃g
      ForestParseRepresentationCotree.graph (Sum.elim f.child g.child (finSumFinEquiv.symm (finSumFinEquiv i)))
    rw [Equiv.symm_apply_apply]

  exact (sumFamilyIso o f.child g.child).trans
    (familyIso o (Sum.elim f.child g.child) (concatenate f g).child e hf)

noncomputable def packIso (o : Operation) (f : Family) (h : 2 ≤ f.count) :
    ForestParseRepresentationCotree.graph (packNode o f h) ≃g familyGraph o f.child := by
  let e : Fin (f.count - 2 + 2) ≃ Fin f.count := finCongr (Nat.sub_add_cancel h)
  exact (nodeFamilyIso o (f.count - 2) (fun i => f.child (Fin.cast (Nat.sub_add_cancel h) i))).trans
    (familyIso o _ f.child e (fun _ => SimpleGraph.Iso.refl))

noncomputable def mergeIso (o : Operation) (s t : Cotree) :
    operationGraph o (ForestParseRepresentationCotree.graph s) (ForestParseRepresentationCotree.graph t) ≃g
      ForestParseRepresentationCotree.graph (merge o s t) :=
  (operationIso o (frontierIso o s) (frontierIso o t)).trans
    ((concatenateIso o (frontier o s) (frontier o t)).trans (packIso o _ _).symm)

private theorem frontierReduced (o : Operation) (t : Cotree) (h : Reduced t) :
    ∀ i, Reduced ((frontier o t).child i) ∧ root ((frontier o t).child i) ≠ some o := by
  cases t with
  | atom => intro i; simp [frontier, singletonFamily, Reduced, root]
  | node p n c =>
    by_cases hp : p = o
    · subst p
      rw [show frontier o (.node o n c) = ⟨n + 2, Nat.zero_lt_succ _, c⟩ by simp [frontier]]
      exact h
    · rw [show frontier o (.node p n c) = singletonFamily (.node p n c) by simp [frontier, hp]]
      intro i
      exact ⟨h, fun he => hp (Option.some.inj he)⟩

theorem mergeCorrect : Targets.MergeCorrect := by
  intro o s t hs ht
  refine ⟨?_, ⟨mergeIso o s t⟩⟩
  have hc : ∀ k, Reduced ((concatenate (frontier o s) (frontier o t)).child k) ∧
      root ((concatenate (frontier o s) (frontier o t)).child k) ≠ some o := by
    intro k
    change Reduced (Sum.elim (frontier o s).child (frontier o t).child (finSumFinEquiv.symm k)) ∧
      root (Sum.elim (frontier o s).child (frontier o t).child (finSumFinEquiv.symm k)) ≠ some o
    cases finSumFinEquiv.symm k with
    | inl j => exact frontierReduced o s hs j
    | inr j => exact frontierReduced o t ht j
  exact fun i => hc _

noncomputable def binaryNodeIso (o : Operation) (s t : RankedParse.Term) :
    RankedParse.graph (.node o s t) ≃g operationGraph o (RankedParse.graph s) (RankedParse.graph t) where
  toEquiv := Equiv.refl _
  map_rel_iff' := by
    rintro (x | x) (y | y) <;> rfl

theorem binaryReducedRepresentation : Targets.BinaryReducedRepresentation := by
  intro t
  induction t with
  | atom => exact ⟨True.intro, ⟨⟨Equiv.refl _, by intro x y; rfl⟩⟩⟩
  | node o s t hs ht =>
    obtain ⟨hs, ⟨es⟩⟩ := hs
    obtain ⟨ht, ⟨et⟩⟩ := ht
    obtain ⟨hr, ⟨e⟩⟩ := mergeCorrect o (normalize s) (normalize t) hs ht
    exact ⟨hr, ⟨(binaryNodeIso o s t).trans ((operationIso o es et).trans e)⟩⟩

theorem normalizationCanonical : Targets.NormalizationCanonical := by
  intro s t h
  obtain ⟨f⟩ := h
  obtain ⟨hs, ⟨es⟩⟩ := binaryReducedRepresentation s
  obtain ⟨ht, ⟨et⟩⟩ := binaryReducedRepresentation t
  exact ForestParseRepresentationCotree.Proof.reducedUniqueness _ _ hs ht
    ⟨es.symm.trans (f.trans et)⟩

end LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationFlatten.Proof
