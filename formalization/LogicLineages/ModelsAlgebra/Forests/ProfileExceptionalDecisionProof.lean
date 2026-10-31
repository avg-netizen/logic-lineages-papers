module
public import LogicLineages.ModelsAlgebra.Forests.ProfileExceptionalDecisionTargets
public import LogicLineages.ModelsAlgebra.Forests.ProfileLanguageEmptyProof
public import LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationGeneralProof
public import Lean.Elab.Tactic.Omega
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.ProfileExceptionalDecision.Proof
open RankedGraphImage ProfileAutomatonEncoding ProfileSourceRegular ForestParseRepresentation

theorem emptyInputCorrect : Targets.EmptyInputCorrect := by
  intro F
  simp [hasEmptyForbidden]

theorem emptyForbiddenCase : Targets.EmptyForbiddenCase := by
  intro B hB
  obtain ⟨H, hH, heH⟩ := hB
  have hnone : ∀ G, ¬ GeneralForbiddenClass B G := by
    intro G hG
    exact hG.2.2 H hH ⟨RankedGraphImage.Proof.emptyEmbedding H G heH⟩
  refine ⟨hnone, ?_⟩
  intro G H hG _
  exact False.elim (hnone G hG)

theorem emptyLanguageCase : Targets.EmptyLanguageCase := by
  intro B hB hnone
  have hevery : ∀ G, GeneralForbiddenClass B G → IsEmpty G.Vertex := by
    intro G hG
    rcases (GeneralProof.generalForbiddenLanguageImage B hB G).mp hG with
      he | ⟨t, ht, _⟩
    · exact he
    · exact False.elim (hnone ⟨t, ht⟩)
  refine ⟨hevery, ?_⟩
  intro G H hG hH
  exact ⟨G, hG, RankedGraphImage.Proof.embedsRefl G,
    ⟨RankedGraphImage.Proof.emptyEmbedding H G (hevery H hH)⟩⟩

theorem exceptionSound : Targets.ExceptionSound := by
  intro F hanswer
  unfold exceptionalDecision at hanswer
  split at hanswer
  · rename_i hempty
    obtain ⟨A, hA, hz⟩ := (emptyInputCorrect F).mp hempty
    have heA : IsEmpty (rawFinite A).Vertex := by
      change IsEmpty (Fin A.1)
      exact ⟨fun x => by have hx := x.isLt; omega⟩
    exact (emptyForbiddenCase (F.map rawFinite)
      ⟨rawFinite A, List.mem_map.mpr ⟨A, hA, rfl⟩, heA⟩).2
  · rename_i hnonempty
    split at hanswer
    · rename_i hl
      have hB : ∀ H ∈ F.map rawFinite, Nonempty H.Vertex := by
        intro H hH
        obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hH
        have hn : A.1 ≠ 0 := by
          intro hz
          exact hnonempty ((emptyInputCorrect F).mpr ⟨A, hA, hz⟩)
        change Nonempty (Fin A.1)
        exact ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
      exact (emptyLanguageCase (F.map rawFinite) hB
        ((ProfileLanguageEmpty.Proof.sourceEmptyCorrect F).mp hl)).2
    · simp at hanswer

end LogicLineages.ModelsAlgebra.Forests.ProfileExceptionalDecision.Proof
