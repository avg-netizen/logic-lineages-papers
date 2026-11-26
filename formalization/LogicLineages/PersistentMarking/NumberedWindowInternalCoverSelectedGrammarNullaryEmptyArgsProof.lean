module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNullaryTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOpenBaseProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWeakDepthInductionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthObservationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenMemberConsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceInversionSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNullaryEmptyArgsProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalOriginalOrderProof (actualOriginalOrderIntroduction)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalSourceInversionSupportProof (onEquality)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb z suc zRelabel bindEmbedding liftBind varBind)
open ID1Completion.InternalTagArithmeticSupportProof (refl)
open ID1Completion.InternalAdditionLawsProof (impSubst leftZero)
open NumberedWindowInternalSparsePassWindowSyntaxProof (memberSubst)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenMemberConsProof (headMember)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalCoverArgumentCellsTargets (axisInclusion)
open NumberedWindowInternalCoverSelectedGrammarWidthTargets (observed)
open NumberedWindowInternalCoverSelectedGrammarWidthObservationProof (observationCases)
open NumberedWindowInternalCoverSelectedGrammarWidthSyntaxProof (observedRename)
open NumberedWindowInternalCoverSelectedGrammarOpenBaseProof (exact_OpenSelectedGrammarBaseSplit)
open NumberedWindowInternalCoverSelectedGrammarWeakDepthInductionProof (exact_OpenSelectedGrammarWeakDepth)
open NumberedWindowInternalCoverSelectedGrammarNullaryTargets

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem fromZero (d H K M state ts args base baseTerms baseArgs : OTerm α)
    (actual : Nonempty (Derivation body Γ (observed d H K M state ts args)))
    (prior : Nonempty (Derivation body Γ (observed z H K M base baseTerms baseArgs))) :
    Nonempty (Derivation body Γ (memberGraph args z)) := by
  have small : Nonempty (Derivation body Γ (ltF z (suc d))) := by
    apply actualOriginalOrderIntroduction body α Γ z (suc d) d
    rw [onEquality]
    exact ⟨leftZero (suc d)⟩
  obtain ⟨inc⟩ := exact_OpenSelectedGrammarWeakDepth body α Γ z d H K M base baseTerms baseArgs
    state ts args small prior actual
  obtain ⟨prior⟩ := prior
  have t := Derivation.conjunctionRight prior
  obtain ⟨split⟩ := exact_OpenSelectedGrammarBaseSplit body α Γ base baseTerms baseArgs H K M
    ⟨Derivation.conjunctionLeft prior⟩ ⟨Derivation.conjunctionLeft t⟩ ⟨Derivation.conjunctionRight t⟩
  obtain ⟨hit⟩ := headMember baseArgs z z z
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight split)⟩ ⟨refl z⟩
  have row : Derivation body Γ (axisInclusion baseArgs args) := Derivation.conjunctionRight inc
  have law : Derivation body Γ ((memberGraph baseArgs z).imp (memberGraph args z)) := by
    simpa only [instantiate,bindEmbedding,impSubst,memberSubst,liftBind,varBind] using
      (Derivation.universalElimination (emb z) row)
  exact ⟨Derivation.implicationElimination law hit⟩

theorem exact_OpenSelectedGrammarEmptyArgs : ExactOpenSelectedGrammarEmptyArgs := by
  intro body α Γ d H K M state ts args actual
  apply observationCases z H K M _
  intro β j Δ base baseTerms baseArgs keep prior
  rw [graphRename,zRelabel]
  have actual' := renameInto actual j Δ keep
  rw [observedRename] at actual'
  simp only [zRelabel] at prior
  exact fromZero (d.relabel j) (H.relabel j) (K.relabel j) (M.relabel j)
    (state.relabel j) (ts.relabel j) (args.relabel j) base baseTerms baseArgs actual' prior

#print axioms exact_OpenSelectedGrammarEmptyArgs

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNullaryEmptyArgsProof
