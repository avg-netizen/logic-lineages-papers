module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionIntroductionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalFiniteBlocks
open InternalGraphCompositionSyntaxProof InternalFiniteBlocksProof InternalTagArithmeticSyntaxProof

theorem actualOriginalCompositionIntroduction : InternalGraphCompositionTargets.ActualOriginalCompositionIntroduction := by
  intro body m n α Gamma f g out xs ys ⟨df⟩ hg
  rw [actualOriginalCompositionInstance]
  apply actualFiniteExistentialIntroduction body α n Gamma _ (fun i => emb (ys i))
  rw [matrixInstantiate]
  obtain ⟨dg⟩ := (actualOriginalFiniteConjunction body α n Gamma
    (fun i => OrdinaryArithmetic.applyGraph (g i) (ys i) xs)).mpr hg
  exact ⟨Derivation.conjunctionIntroduction df dg⟩

theorem actualOriginalCompositionElimination : InternalGraphCompositionTargets.ActualOriginalCompositionElimination := by
  intro body m n α Gamma f g out xs psi h e
  rw [actualOriginalCompositionInstance] at h
  exact actualFiniteExistentialElimination body α n Gamma _ psi h e
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionIntroductionProof
