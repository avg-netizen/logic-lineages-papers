module
public import LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationGeneralTargets
public import LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationProof
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentation.GeneralProof
open GraphBridge RankedParse RankedGraphImage

private theorem avoidanceForward (B : List FiniteGraph) (G H : FiniteGraph)
    (e : G.edges ≃g H.edges) (h : GeneralForbiddenClass B G) : GeneralForbiddenClass B H := by
  have transfer {V : Type} (A : SimpleGraph V) (ha : ¬ Nonempty (A ↪g G.edges)) :
      ¬ Nonempty (A ↪g H.edges) := by
    rintro ⟨f⟩
    exact ha ⟨f.trans e.symm.toEmbedding⟩
  exact ⟨transfer fourPath h.1, transfer fourCycle h.2.1,
    fun A hA => transfer A.edges (h.2.2 A hA)⟩

private theorem emptyForbidden (B : List FiniteGraph)
    (hB : ∀ H ∈ B, Nonempty H.Vertex) (G : FiniteGraph) (hG : IsEmpty G.Vertex) :
    GeneralForbiddenClass B G := by
  have noEmbed {V : Type} (A : SimpleGraph V) (hV : Nonempty V) :
      ¬ Nonempty (A ↪g G.edges) := by
    rintro ⟨f⟩
    exact hG.false (f (Classical.choice hV))
  exact ⟨noEmbed fourPath inferInstance, noEmbed fourCycle inferInstance,
    fun A hA => noEmbed A.edges (hB A hA)⟩

theorem generalForbiddenLanguageImage : GeneralTargets.GeneralForbiddenLanguageImage := by
  classical
  intro B hB G
  constructor
  · intro hG
    by_cases he : IsEmpty G.Vertex
    · exact Or.inl he
    · have hn : Nonempty G.Vertex := not_isEmpty_iff.mp he
      letI : Fintype G.Vertex := Fintype.ofFinite G.Vertex
      obtain ⟨F, ⟨e⟩⟩ := CanonicalOrderProof.canonicalGraphRepresentation
        G.Vertex G.edges hG.1 hG.2.1
      have hF : Nonempty F.Carrier := ⟨e (Classical.choice hn)⟩
      obtain ⟨t, ⟨f⟩⟩ := Proof.forestRankedRepresentation F hF
      let q : G.edges ≃g graph t := e.trans f
      have ht : GeneralForbiddenLanguage B t := avoidanceForward B G (evalFinite t) q hG
      exact Or.inr ⟨t, ht, ⟨q⟩⟩
  · rintro (he | ⟨t, ht, ⟨e⟩⟩)
    · exact emptyForbidden B hB G he
    · exact avoidanceForward B (evalFinite t) G e.symm ht

theorem generalForbiddenIdealCover : GeneralTargets.GeneralForbiddenIdealCover := by
  intro B hB ι _ _ I hI hL
  have hcover : ∀ G, GeneralForbiddenClass B G ↔ ∃ i, Image (I i) G :=
    RankedGraphImage.Proof.imageCoverFromLanguage ι I (GeneralForbiddenLanguage B)
      (GeneralForbiddenClass B) hL (generalForbiddenLanguageImage B hB)
  exact ⟨hcover, RankedGraphImage.Proof.imageCover ι I (GeneralForbiddenClass B) hI hcover⟩

end LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentation.GeneralProof
