module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowSortedRevision
public import LogicLineages.ComputabilityKnowledge.GorbowSortedSyntaxCodeProof
public import LogicLineages.ComputabilityKnowledge.GorbowRevisionSemanticsProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowSortedRevisionProof
open GorbowSyntax GorbowSortedSyntaxCode GorbowSortedRevision

theorem fixedInterpretation : Comparators.GorbowSortedRevision.FixedInterpretation :=
  ⟨GorbowRevisionSemanticsProof.singletonCalibration,GorbowRevisionSemanticsProof.fixedMinus,
    GorbowRevisionSemanticsProof.modelClauses⟩

private theorem imageAt (g : Ground) (P : Extension) (σ : Sentence) :
    revise g P (formulaCode σ) ↔ σ.realize (interpretation g P) Fin.elim0 := by
  constructor
  · rintro ⟨τ,he,ht⟩
    have hτσ : τ=σ := GorbowSortedSyntaxCodeProof.actualInjection.1 0 he
    simpa only [hτσ] using ht
  · intro h
    exact ⟨σ,rfl,h⟩

theorem exactImage : Comparators.GorbowSortedRevision.ExactImage := by
  intro g P
  refine ⟨imageAt g P,?_⟩
  intro code h
  obtain ⟨σ,he,ht⟩ := h
  exact ⟨σ,he.symm⟩

theorem termExclusion : Comparators.GorbowSortedRevision.TermExclusion := by
  intro g P n t h
  obtain ⟨σ,he,ht⟩ := h
  exact GorbowSortedSyntaxCodeProof.actualInjection.2.2.1 0 n σ t he

theorem successorCalibration : Comparators.GorbowSortedRevision.SuccessorCalibration := by
  intro g initial n σ
  simp only [truthSentence,allKnowledgeSentence,knowledgeSentence,formulaQuote,Formula.realize,numeral_realize]
  change (revise g (extensions g initial n) (formulaCode σ) ↔ _) ∧
    (revise g (extensions g initial n) (formulaCode σ) ↔ _) ∧
    (∀ a, (a=0 ∧ revise g (extensions g initial n) (formulaCode σ)) ↔ _)
  simp only [imageAt,stage]
  exact ⟨True.intro,True.intro,fun _ => True.intro⟩

theorem positiveDistribution : Comparators.GorbowSortedRevision.PositiveDistribution := by
  intro g initial n σ τ hi hs
  change revise g (extensions g initial n) (formulaCode τ)
  apply (imageAt g _ τ).mpr
  have hf := (imageAt g _ (.imp σ τ)).mp hi
  exact hf ((imageAt g _ σ).mp hs)

theorem coreSoundness : Comparators.GorbowSortedRevision.CoreSoundness := by
  intro g initial k n φ p v
  exact GorbowPACoreProof.proofSoundness n φ p (stage g initial k) v

theorem gorbowSortedRevision : Comparators.GorbowSortedRevision.Target :=
  ⟨fixedInterpretation,exactImage,termExclusion,successorCalibration,positiveDistribution,coreSoundness⟩
end LogicLineages.ComputabilityKnowledge.GorbowSortedRevisionProof
