module
public import LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationTargets
public import LogicLineages.ModelsAlgebra.Forests.GraphJEPProof
public import LogicLineages.ModelsAlgebra.Forests.RankedImageCoverCompletionProof
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentation.Proof
open GraphBridge RankedParse RankedGraphImage

private def singletonRealizes (F : FiniteOrderForest) (r : F.Carrier) :
    Realizes F {r} .atom where
  map := fun _ => r
  injective := by intro x y _; cases x; cases y; rfl
  adjacency := by intro x y; simp [Adj]
  image := by intro y; simp [Leaf, eq_comm]

private def combine {F : FiniteOrderForest} [DecidableEq F.Carrier] {S T : Finset F.Carrier} {s t : Term}
    (f : Realizes F S s) (g : Realizes F T t) (o : Operation)
    (hd : Disjoint S T)
    (hc : ∀ x ∈ S, ∀ y ∈ T, (comparabilityGraph F).Adj x y ↔ o = .join) :
    Realizes F (S ∪ T) (.node o s t) where
  map := Sum.elim f.map g.map
  injective := by
    intro x y h
    cases x with
    | inl x => cases y with
      | inl y => exact congrArg Sum.inl (f.injective h)
      | inr y =>
        have hx := (f.image (f.map x)).mp ⟨x, rfl⟩
        have hy := (g.image (g.map y)).mp ⟨y, rfl⟩
        change f.map x = g.map y at h
        exact False.elim ((Finset.disjoint_left.mp hd) hx (by simpa only [h] using hy))
    | inr x => cases y with
      | inl y =>
        have hx := (g.image (g.map x)).mp ⟨x, rfl⟩
        have hy := (f.image (f.map y)).mp ⟨y, rfl⟩
        change g.map x = f.map y at h
        exact False.elim ((Finset.disjoint_left.mp hd) hy (by simpa only [h] using hx))
      | inr y => exact congrArg Sum.inr (g.injective h)
  adjacency := by
    intro x y
    cases x with
    | inl x => cases y with
      | inl y => exact f.adjacency x y
      | inr y => exact hc _ ((f.image _).mp ⟨x, rfl⟩) _ ((g.image _).mp ⟨y, rfl⟩)
    | inr x => cases y with
      | inl y =>
        exact ((comparabilityGraph F).adj_comm _ _).trans
          (hc _ ((f.image _).mp ⟨y, rfl⟩) _ ((g.image _).mp ⟨x, rfl⟩))
      | inr y => exact g.adjacency x y
  image := by
    intro y
    constructor
    · rintro ⟨x, hx⟩
      cases x with
      | inl x => exact Finset.mem_union.mpr (Or.inl ((f.image y).mp ⟨x, hx⟩))
      | inr x => exact Finset.mem_union.mpr (Or.inr ((g.image y).mp ⟨x, hx⟩))
    · intro hy
      rcases Finset.mem_union.mp hy with hy | hy
      · obtain ⟨x, hx⟩ := (f.image y).mpr hy
        exact ⟨.inl x, hx⟩
      · obtain ⟨x, hx⟩ := (g.image y).mpr hy
        exact ⟨.inr x, hx⟩

private theorem subsetRepresentation (F : FiniteOrderForest) (S : Finset F.Carrier)
    (hne : S.Nonempty) : ∃ t, Nonempty (Realizes F S t) := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    obtain ⟨r, hr, hmin⟩ := S.exists_minimal hne
    let A := S.filter (fun x => r ≤ x ∧ x ≠ r)
    let B := S.filter (fun x => ¬ r ≤ x)
    let C : Finset F.Carrier := {r} ∪ A
    have hA : A ⊂ S := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, ?_⟩
      intro he
      have : r ∈ A := he.symm ▸ hr
      simpa [A] using this
    have hB : B ⊂ S := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, ?_⟩
      intro he
      have : r ∈ B := he.symm ▸ hr
      simpa [B] using this
    have hC : ∃ t, Nonempty (Realizes F C t) := by
      by_cases hAn : A.Nonempty
      · obtain ⟨a, ⟨fa⟩⟩ := ih A hA hAn
        have hd : Disjoint ({r} : Finset F.Carrier) A := by simp [A]
        refine ⟨.node .join .atom a, ⟨combine (singletonRealizes F r) fa .join hd ?_⟩⟩
        intro x hx y hy
        have hx : x = r := Finset.mem_singleton.mp hx
        subst x
        have hy' := Finset.mem_filter.mp hy
        change (r ≠ y ∧ (r ≤ y ∨ y ≤ r)) ↔ Operation.join = Operation.join
        exact ⟨fun _ => rfl, fun _ => ⟨Ne.symm hy'.2.2, Or.inl hy'.2.1⟩⟩
      · have he : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hAn
        simpa [C, he] using (show ∃ t, Nonempty (Realizes F {r} t) from
          ⟨.atom, ⟨singletonRealizes F r⟩⟩)
    have hCS : C ⊆ S := by
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · simpa [Finset.mem_singleton.mp hx] using hr
      · exact (Finset.mem_filter.mp hx).1
    have hCr : ∀ x ∈ C, r ≤ x := by
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · simpa [Finset.mem_singleton.mp hx]
      · exact (Finset.mem_filter.mp hx).2.1
    have hd : Disjoint C B := by
      apply Finset.disjoint_left.mpr
      intro x hx hb
      exact (Finset.mem_filter.mp hb).2 (hCr x hx)
    have hsplit : C ∪ B = S := by
      ext x
      constructor
      · intro hx
        rcases Finset.mem_union.mp hx with hx | hx
        · exact hCS hx
        · exact (Finset.mem_filter.mp hx).1
      · intro hx
        by_cases he : x = r
        · subst x; simp [C]
        · by_cases hle : r ≤ x
          · exact Finset.mem_union_left _ (Finset.mem_union_right _
              (Finset.mem_filter.mpr ⟨hx, hle, he⟩))
          · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx, hle⟩)
    obtain ⟨c, ⟨fc⟩⟩ := hC
    by_cases hBn : B.Nonempty
    · obtain ⟨b, ⟨fb⟩⟩ := ih B hB hBn
      have hc : ∀ x ∈ C, ∀ y ∈ B, (comparabilityGraph F).Adj x y ↔
          Operation.union = Operation.join := by
        intro x hx y hy
        have hy' := Finset.mem_filter.mp hy
        have hny : ¬ r ≤ y := hy'.2
        change (x ≠ y ∧ (x ≤ y ∨ y ≤ x)) ↔ Operation.union = Operation.join
        constructor
        · rintro ⟨_, hxy | hyx⟩
          · exact False.elim (hny ((hCr x hx).trans hxy))
          · rcases F.forest (hCr x hx) hyx with hry | hyr
            · exact False.elim (hny hry)
            · exact False.elim (hny (hmin hy'.1 hyr))
        · intro h; cases h
      exact ⟨.node .union c b, ⟨hsplit ▸ combine fc fb .union hd hc⟩⟩
    · have he : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hBn
      have hCe : C = S := by simpa [he] using hsplit
      exact ⟨c, ⟨hCe ▸ fc⟩⟩

theorem forestRankedRepresentation : Targets.ForestRankedRepresentation := by
  classical
  intro F hF
  letI := hF
  obtain ⟨t, ⟨f⟩⟩ := subsetRepresentation F Finset.univ Finset.univ_nonempty
  have hs : Function.Surjective f.map := by
    intro y
    exact (f.image y).mpr (Finset.mem_univ y)
  let e : graph t ≃g comparabilityGraph F := {
    toEquiv := Equiv.ofBijective f.map ⟨f.injective, hs⟩
    map_rel_iff' := by intro x y; exact f.adjacency x y }
  exact ⟨t, ⟨e.symm⟩⟩

private theorem emptyForbidden (U : List FiniteOrderForest)
    (hU : ∀ B ∈ U, Nonempty B.Carrier) (G : FiniteGraph) (hG : IsEmpty G.Vertex) :
    ForbiddenClass U G := by
  have noEmbed {V : Type} (B : SimpleGraph V) (hV : Nonempty V) :
      ¬ Nonempty (B ↪g G.edges) := by
    rintro ⟨f⟩
    exact hG.false (f (Classical.choice hV))
  exact ⟨noEmbed fourPath inferInstance, noEmbed fourCycle inferInstance,
    fun B hB => noEmbed (comparabilityGraph B) (hU B hB)⟩

theorem actualForbiddenLanguageImage : Targets.ActualForbiddenLanguageImage := by
  classical
  intro U hU G
  constructor
  · intro hG
    by_cases he : IsEmpty G.Vertex
    · exact Or.inl he
    · have hn : Nonempty G.Vertex := not_isEmpty_iff.mp he
      obtain ⟨F, _, ⟨e⟩⟩ := GraphJEPProof.forbiddenGraphRepresented U (bridgeGraph G) hG
      have hF : Nonempty F.Carrier := ⟨e (Classical.choice hn)⟩
      obtain ⟨t, ⟨f⟩⟩ := forestRankedRepresentation F hF
      let q : G.edges ≃g graph t := e.trans f
      have ht : ForbiddenLanguage U t :=
        (GraphJEPProof.graphAvoidanceIsoInvariant U (bridgeGraph G)
          (bridgeGraph (evalFinite t)) q).mp hG
      exact Or.inr ⟨t, ht, ⟨q⟩⟩
  · rintro (he | ⟨t, ht, ⟨e⟩⟩)
    · exact emptyForbidden U hU G he
    · exact (GraphJEPProof.graphAvoidanceIsoInvariant U (bridgeGraph G)
        (bridgeGraph (evalFinite t)) e).mpr ht

theorem actualForbiddenIdealCover : Targets.ActualForbiddenIdealCover := by
  intro U hU ι _ _ I hI hL
  have hcover : ∀ G, ForbiddenClass U G ↔ ∃ i, Image (I i) G :=
    RankedGraphImage.Proof.imageCoverFromLanguage ι I (ForbiddenLanguage U)
      (ForbiddenClass U) hL (actualForbiddenLanguageImage U hU)
  exact ⟨hcover, RankedGraphImage.Proof.imageCover ι I (ForbiddenClass U) hI hcover⟩

end LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentation.Proof
