module
public import LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationBinaryTargets
public import LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationFlattenProof
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationBinary.Proof
open RankedParse ForestParseRepresentationCotree ForestParseRepresentationFlatten
open ForestParseRepresentationFlatten.Proof

/-- Renaming labels does not change the actual leaf-occurrence set. -/
def renamePositions {I J : Type} (f : I → J) : (q : Shape I) → Positions q ≃ Positions (rename f q)
  | .leaf _ => Equiv.refl _
  | .node p q => Equiv.sumCongr (renamePositions f p) (renamePositions f q)

theorem renameLabel {I J : Type} (f : I → J) (q : Shape I) (x : Positions q) :
    label (rename f q) (renamePositions f q x) = f (label q x) := by
  induction q with
  | leaf i => rfl
  | node p q hp hq => cases x with
    | inl x => exact hp x
    | inr x => exact hq x

theorem renameBijective {I J : Type} (e : I ≃ J) (q : Shape I)
    (h : Function.Bijective (label q)) : Function.Bijective (label (rename e q)) := by
  have he : (label (rename e q)) ∘ (renamePositions e q) = e ∘ label q :=
    funext (renameLabel e q)
  have hh : Function.Bijective ((label (rename e q)) ∘ (renamePositions e q)) := by
    rw [he]
    exact e.bijective.comp h
  constructor
  · intro x y hxy
    have hhxy : (renamePositions e q).symm x = (renamePositions e q).symm y :=
      hh.injective (by simpa using hxy)
    exact (renamePositions e q).symm.injective hhxy
  · intro j
    obtain ⟨x, hx⟩ := hh.surjective j
    exact ⟨renamePositions e q x, hx⟩

theorem graftRename {I J : Type} (f : I → J) (o : Operation) (r : J → Term) (q : Shape I) :
    graft o r (rename f q) = graft o (r ∘ f) q := by
  induction q with
  | leaf i => rfl
  | node p q hp hq => simp only [rename, graft, hp, hq]

noncomputable def shapeIso {I : Type} (o : Operation) (r : I → Term) (c : I → Cotree)
    (f : ∀ i, RankedParse.graph (r i) ≃g ForestParseRepresentationCotree.graph (c i)) :
    (q : Shape I) → RankedParse.graph (graft o r q) ≃g
      familyGraph o (fun x : Positions q => c (label q x))
  | .leaf i => (f i).trans {
      toEquiv := (Equiv.uniqueSigma (fun _ : Unit => ForestParseRepresentationCotree.Leaf (c i))).symm
      map_rel_iff' := by
        intro x y
        change familyAdj o (fun _ : Unit => c i) ⟨(), x⟩ ⟨(), y⟩ ↔ ForestParseRepresentationCotree.Adj (c i) x y
        simp [familyAdj] }
  | .node p q => (binaryNodeIso o (graft o r p) (graft o r q)).trans
      ((operationIso o (shapeIso o r c f p) (shapeIso o r c f q)).trans
        ((sumFamilyIso o (fun x => c (label p x)) (fun y => c (label q y))).trans
          (familyIso o _ (fun x : Positions (.node p q) => c (label (.node p q) x))
            (Equiv.refl _) (fun x => by cases x <;> exact SimpleGraph.Iso.refl))))

theorem expansionSound : Targets.ExpansionSound := by
  intro t C h
  induction h with
  | atom => exact ⟨⟨Equiv.refl _, by intro x y; rfl⟩⟩
  | @node o n c r q hc hb ih =>
    classical
    let e : Positions q ≃ Fin (n + 2) := Equiv.ofBijective (label q) hb
    exact ⟨(shapeIso o r c (fun i => Classical.choice (ih i)) q).trans
      ((familyIso o (fun x => c (label q x)) c e (fun _ => SimpleGraph.Iso.refl)).trans
        (nodeFamilyIso o n c).symm)⟩


private def Witness {I : Type} (o : Operation) (t : Term) (c : I → Cotree) : Prop :=
  ∃ (r : I → Term) (q : Shape I), (∀ i, Expansion (r i) (c i)) ∧
    Function.Bijective (label q) ∧ graft o r q = t

private theorem witnessReindex {I J : Type} (o : Operation) (t : Term)
    (c : I → Cotree) (d : J → Cotree) (e : I ≃ J) (he : ∀ i, c i = d (e i))
    (h : Witness o t c) : Witness o t d := by
  obtain ⟨r, q, hc, hb, ht⟩ := h
  refine ⟨r ∘ e.symm, rename e q, ?_, renameBijective e q hb, ?_⟩
  · intro j
    have hj := hc (e.symm j)
    rw [he] at hj
    simpa using hj
  · rw [graftRename]
    simpa [Function.comp_def] using ht

private theorem witnessSingleton (o : Operation) (t : Term) (C : Cotree)
    (h : Expansion t C) : Witness o t (singletonFamily C).child := by
  change Witness o t (fun _ : Fin 1 => C)
  refine ⟨fun _ => t, .leaf 0, fun _ => h, ?_, rfl⟩
  constructor
  · intro x y _; exact @Subsingleton.elim Unit _ x y
  · intro i; exact ⟨(), Subsingleton.elim _ _⟩

private theorem witnessFrontier (o : Operation) (t : Term) (C : Cotree)
    (h : Expansion t C) : Witness o t (frontier o C).child := by
  cases C with
  | atom => exact witnessSingleton o t .atom h
  | node p n c =>
    by_cases hp : p = o
    · subst p
      rw [show frontier o (.node o n c) = ⟨n + 2, Nat.zero_lt_succ _, c⟩ by simp [frontier]]
      cases h with
      | node r q hc hb => exact ⟨r, q, hc, hb, rfl⟩
    · rw [show frontier o (.node p n c) = singletonFamily (.node p n c) by simp [frontier, hp]]
      exact witnessSingleton o t _ h

private theorem combinedBijective {I J : Type} (p : Shape I) (q : Shape J)
    (hp : Function.Bijective (label p)) (hq : Function.Bijective (label q)) :
    Function.Bijective (label (.node (rename Sum.inl p) (rename Sum.inr q) : Shape (Sum I J))) := by
  let e := Equiv.sumCongr (renamePositions (Sum.inl : I → Sum I J) p)
    (renamePositions (Sum.inr : J → Sum I J) q)
  let f := Equiv.sumCongr (Equiv.ofBijective (label p) hp) (Equiv.ofBijective (label q) hq)
  have he : (label (.node (rename Sum.inl p) (rename Sum.inr q))) ∘ e = f := by
    funext x
    cases x with
    | inl x => exact renameLabel Sum.inl p x
    | inr y => exact renameLabel Sum.inr q y
  have hh : Function.Bijective ((label (.node (rename Sum.inl p) (rename Sum.inr q))) ∘ e) := by
    rw [he]; exact f.bijective
  constructor
  · intro x y hxy
    exact e.symm.injective (hh.injective (by simpa using hxy))
  · intro j
    obtain ⟨x, hx⟩ := hh.surjective j
    exact ⟨e x, hx⟩

private theorem witnessSum {I J : Type} (o : Operation) (s t : Term)
    (c : I → Cotree) (d : J → Cotree) (hs : Witness o s c) (ht : Witness o t d) :
    Witness o (.node o s t) (Sum.elim c d) := by
  obtain ⟨r, p, hc, hp, hs⟩ := hs
  obtain ⟨u, q, hd, hq, ht⟩ := ht
  refine ⟨Sum.elim r u, .node (rename Sum.inl p) (rename Sum.inr q), ?_, combinedBijective p q hp hq, ?_⟩
  · intro i
    cases i with
    | inl i => exact hc i
    | inr j => exact hd j
  · simp only [graft, graftRename]
    change Term.node o (graft o r p) (graft o u q) = _
    rw [hs, ht]

private theorem witnessMerge (o : Operation) (s t : Term) (C D : Cotree)
    (hs : Expansion s C) (ht : Expansion t D) : Expansion (.node o s t) (merge o C D) := by
  let f := concatenate (frontier o C) (frontier o D)
  have hf : Witness o (.node o s t) f.child :=
    witnessReindex o _ _ f.child finSumFinEquiv
      (fun i => by
        change Sum.elim (frontier o C).child (frontier o D).child i =
          Sum.elim (frontier o C).child (frontier o D).child (finSumFinEquiv.symm (finSumFinEquiv i))
        rw [Equiv.symm_apply_apply])
      (witnessSum o s t _ _ (witnessFrontier o s C hs) (witnessFrontier o t D ht))
  let h : 2 ≤ f.count := Nat.add_le_add (frontier o C).positive (frontier o D).positive
  let e : Fin f.count ≃ Fin (f.count - 2 + 2) := (finCongr (Nat.sub_add_cancel h)).symm
  have hh : Witness o (.node o s t) (fun i => f.child (Fin.cast (Nat.sub_add_cancel h) i)) :=
    witnessReindex o _ f.child _ e (fun i => by simp [e]) hf
  obtain ⟨r, q, hc, hb, he⟩ := hh
  rw [← he]
  exact Expansion.node r q hc hb

theorem normalizationExpansion : Targets.NormalizationExpansion := by
  intro t
  induction t with
  | atom => exact Expansion.atom
  | node o s t hs ht => exact witnessMerge o s t _ _ hs ht

theorem expansionTransport : Targets.ExpansionTransport := by
  intro C D h
  induction h with
  | atom => intro t ht; exact ht
  | @node o n m c d e hc ih =>
    intro t ht
    cases ht with
    | node r q hr hb =>
      have hw : Witness o (graft o r q) (fun i => d (e i)) :=
        ⟨r, q, fun i => ih i _ (hr i), hb, rfl⟩
      have hw' := witnessReindex o _ (fun i => d (e i)) d e (fun _ => rfl) hw
      obtain ⟨u, p, hu, hp, he⟩ := hw'
      rw [← he]
      exact Expansion.node u p hu hp

theorem binaryCharacterization : Targets.BinaryCharacterization := by
  intro t C hC
  constructor
  · intro h
    obtain ⟨f⟩ := h
    obtain ⟨hn, ⟨en⟩⟩ := ForestParseRepresentationFlatten.Proof.binaryReducedRepresentation t
    have hi := ForestParseRepresentationCotree.Proof.reducedUniqueness _ _ hn hC ⟨en.symm.trans f⟩
    exact expansionTransport _ _ hi t (normalizationExpansion t)
  · exact expansionSound t C

end LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationBinary.Proof
