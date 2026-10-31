module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealGraphDecisionTargets
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealSourceCodeStatementChecks
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealImageInclusionStatementChecks
public import LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationGeneralStatementChecks
public import LogicLineages.ModelsAlgebra.Forests.ProfileExceptionalDecisionStatementChecks
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealGraphDecision.Proof
open ProfileAutomatonEncoding ProfileSourceRegular ProfileExceptionalDecision RankedIdealSourceCode RankedIdealRegularCode RankedGraphImage ForestParseRepresentation
 theorem noEmpty (F : List RawGraph) (h : hasEmptyForbidden F ≠ true) :
    ∀ H ∈ F.map rawFinite, Nonempty H.Vertex := by
  intro H hH
  obtain ⟨A,hA,rfl⟩ := List.mem_map.mp hH
  have hn : A.1 ≠ 0 := by
    intro hz
    exact h ((ProfileExceptionalDecision.StatementChecks.emptyInputCorrect F).mpr ⟨A,hA,hz⟩)
  exact ⟨⟨0,Nat.pos_of_ne_zero hn⟩⟩
 theorem emptyForbidden (F : List RawGraph) (h : hasEmptyForbidden F = true) :
    GraphJEP (GeneralForbiddenClass (F.map rawFinite)) := by
  obtain ⟨A,hA,hz⟩ := (ProfileExceptionalDecision.StatementChecks.emptyInputCorrect F).mp h
  apply (ProfileExceptionalDecision.StatementChecks.emptyForbiddenCase (F.map rawFinite) ?_).2
  refine ⟨rawFinite A,List.mem_map.mpr ⟨A,hA,rfl⟩,?_⟩
  change IsEmpty (Fin A.1)
  rw [hz]
  infer_instance
 theorem sourceImage (F : List RawGraph) (h : hasEmptyForbidden F ≠ true) G :
    GeneralForbiddenClass (F.map rawFinite) G ↔ Image (language (sourceCode F)) G := by
  have he : language (sourceCode F) = GeneralForbiddenLanguage (F.map rawFinite) :=
    funext (fun t => propext (RankedIdealSourceCode.StatementChecks.sourceCodeExact F t))
  rw [he]
  exact GeneralStatementChecks.generalForbiddenLanguageImage _ (noEmpty F h) G
 theorem coverCriterion (F : List RawGraph) (h : hasEmptyForbidden F ≠ true)
    (hne : sourceCover F ≠ []) :
    GraphJEP (GeneralForbiddenClass (F.map rawFinite)) ↔
      ∃ B ∈ sourceCover F, ∀ G, Image (language (sourceCode F)) G → Image (language B) G := by
  let I := fun i : Fin (sourceCover F).length => language ((sourceCover F)[i])
  have hlen : 0 < (sourceCover F).length := List.length_pos_iff.mpr hne
  letI : Nonempty (Fin (sourceCover F).length) := ⟨⟨0,hlen⟩⟩
  have hi : ∀ i, IsIdeal (I i) := by
    intro i
    exact RankedIdealSourceCode.StatementChecks.sourceCoverIdeals F _ (List.getElem_mem _)
  have hc : ∀ t, GeneralForbiddenLanguage (F.map rawFinite) t ↔ ∃ i, I i t := by
    intro t
    constructor
    · intro ht
      obtain ⟨B,hB,hBt⟩ := (RankedIdealSourceCode.StatementChecks.sourceCoverExact F t).mp ht
      obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hB
      refine ⟨⟨i,hi⟩,?_⟩
      change language ((sourceCover F)[i]) t
      rw [he]
      exact hBt
    · rintro ⟨i,ht⟩
      exact (RankedIdealSourceCode.StatementChecks.sourceCoverExact F t).mpr
        ⟨(sourceCover F)[i],List.getElem_mem _,ht⟩
  have crit := (GeneralStatementChecks.generalForbiddenIdealCover _ (noEmpty F h)
    (Fin (sourceCover F).length) I hi hc).2.2
  constructor
  · intro hj
    obtain ⟨i,hei⟩ := crit.mp hj
    refine ⟨(sourceCover F)[i],List.getElem_mem _,?_⟩
    intro G hG
    exact (hei G).mp ((sourceImage F h G).mpr hG)
  · rintro ⟨B,hB,hinc⟩
    obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hB
    apply crit.mpr
    refine ⟨⟨i,hi⟩,?_⟩
    intro G
    change GeneralForbiddenClass (F.map rawFinite) G ↔ Image (language ((sourceCover F)[i])) G
    rw [he]
    constructor
    · intro hG
      exact hinc G ((sourceImage F h G).mp hG)
    · intro hG
      apply (sourceImage F h G).mpr
      rcases hG with hempty | ⟨t,ht,e⟩
      · exact Or.inl hempty
      · exact Or.inr ⟨t,(RankedIdealSourceCode.StatementChecks.sourceCodeExact F t).mpr
          ((RankedIdealSourceCode.StatementChecks.sourceCoverExact F t).mpr ⟨B,hB,ht⟩),e⟩
 theorem graphDecisionExact : Targets.GraphDecisionExact := by
  intro F
  by_cases he : hasEmptyForbidden F = true
  · constructor
    · intro _; exact emptyForbidden F he
    · intro _; simp [graphDecision,he]
  · by_cases hc : (sourceCover F).isEmpty = true
    · have hnolang := (RankedIdealSourceCode.StatementChecks.sourceCoverEmpty F).mp (List.isEmpty_iff.mp hc)
      have hj := (ProfileExceptionalDecision.StatementChecks.emptyLanguageCase _ (noEmpty F he)
        (by rintro ⟨t,ht⟩; exact hnolang t ht)).2
      constructor
      · intro _; exact hj
      · intro _; simp [graphDecision,he,hc]
    · have hn : sourceCover F ≠ [] := fun hz => hc (List.isEmpty_iff.mpr hz)
      rw [graphDecision,if_neg he,if_neg hc,List.any_eq_true]
      rw [coverCriterion F he hn]
      constructor
      · rintro ⟨B,hB,hinc⟩
        exact ⟨B,hB,(RankedIdealImageInclusion.StatementChecks.imageInclusionExact _ _).mp hinc⟩
      · rintro ⟨B,hB,hinc⟩
        exact ⟨B,hB,(RankedIdealImageInclusion.StatementChecks.imageInclusionExact _ _).mpr hinc⟩
end LogicLineages.ModelsAlgebra.Forests.RankedIdealGraphDecision.Proof
