module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSingletonTypeArgumentTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSingletonTypeArgumentOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSingletonTypeArgumentOccurrenceProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverOrdinaryMeasureCutProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverOrdinaryMeasureArgumentProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaMeasureRowBumpProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeadWindowSelectedProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredDispatchRenameProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLocalOwnReportRenameProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnScratchProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthObservationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeavesOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnTermPartProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceInversionSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSingletonTypeArgumentScratchProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (trans congSuc addZero addSucc)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalOriginalOrderProof (actualOriginalOrderIntroduction)
open ID1Completion.InternalSourceInversionSupportProof (onEquality)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (rawConsRename)
open NumberedWindowInternalCoverTypeLeavesOpenDataProof (termRename)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (headsTerm typesTerm measurePair)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalCoverRefinedInductionDispatchTargets (Programs ParentRow)
open NumberedWindowInternalCoverLocalOwnReportRenameProof (moveParent)
open NumberedWindowInternalCoverMeasuredDispatchRenameProof (keepThrough moveStoredK moveParentPair)
open NumberedWindowInternalCoverSelectedGrammarWidthObservationProof (observationCases)
open NumberedWindowInternalCoverSelectedGrammarWidthSyntaxProof (observedRename)
open NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnTargets (ordinaryKey OrdinaryOwnInputs)
open NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnTermPartProof (ordinaryRename)
open NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnScratchProof (exact_OpenSelectedGrammarOrdinaryScratch)
open NumberedWindowInternalCoverOrdinaryMeasureCutProof (exact_OpenCoverOrdinaryMeasureCut)
open NumberedWindowInternalCoverOrdinaryMeasureArgumentProof (exact_OpenOrdinaryBumpFromArgument)
open NumberedWindowInternalCoverLambdaMeasureRowBumpProof (exact_OpenCoverLambdaBumpPair)
open NumberedWindowInternalCoverHeadWindowSelectedProof (exact_OpenCoverHeadFittedWindow)
open NumberedWindowInternalCoverNumberedTypeWindowTargets (numberedTypeBase)
open NumberedWindowInternalCoverLambdaLexicalWindowTargets (lambdaLexicalBase)
open NumberedWindowInternalCoverLambdaBoundCoherenceTargets (lexicalFittedPrograms)
open NumberedWindowInternalCoverNumberedMeasureSelectedTargets (numberedMeasureBase)
open NumberedWindowInternalCoverSingletonTypeArgumentOpenProof
  (singletonCodePair exact_OpenCoverSingletonTypeArgument)
open NumberedWindowInternalCoverSingletonTypeArgumentOccurrenceProof
  (exact_OpenCoverSingletonTypeOccurrence)
open NumberedWindowInternalCoverSingletonTypeArgumentTargets

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem selfWeak (x : OTerm α) : Nonempty (Derivation body Γ (ltF x (suc x))) := by
  apply actualOriginalOrderIntroduction body α Γ x (suc x) z
  rw [onEquality]
  exact ⟨trans (addSucc x z) (congSuc (addZero x))⟩

private theorem atObservedScopes (P : Programs) (s : Settings) (h ty p vertices ctx result : OTerm α)
    (row : ParentRow P s body Γ (ordinaryKey h (singletonTypeKey ty)) p vertices ctx result)
    (head : Nonempty (Derivation body Γ (memberGraph (headsTerm s α) h)))
    (inK : Nonempty (Derivation body Γ (memberGraph (typesTerm s α) ty)))
    (pair : Nonempty (Derivation body Γ (measurePair p (numeral 2) z))) :
    Nonempty (Derivation body Γ (memberGraph vertices (ordinaryKey h (singletonTypeKey ty)))) := by
  let Q := memberGraph vertices (ordinaryKey h (singletonTypeKey ty))
  apply observationCases (numeral 1) (headsTerm s α) (typesTerm s α) z Q
  intro β j Δ first fst fa keep before
  apply observationCases (numeral 2) (headsTerm s β) (typesTerm s β) z (Q.relabel j)
  intro γ g Ξ later lt la retain after
  let q := g ∘ j
  have both := keepThrough j g keep retain
  have before' := renameInto before g Ξ retain
  simp only [observedRename,headsTerm,typesTerm,numeralRename,zRelabel] at before'
  simp only [headsTerm,typesTerm,numeralRename,zRelabel] at after
  have ht := moveStoredK s q both ty inK
  have args := exact_OpenCoverSingletonTypeOccurrence body γ Ξ (headsTerm s γ) (typesTerm s γ)
    (ty.relabel q) (first.relabel g) (fst.relabel g) (fa.relabel g) later lt la ht before' after
  have hd := renameInto head q Ξ both
  simp only [graphRename,headsTerm,numeralRename] at hd
  have pp := moveParentPair q both p (numeral 2) z pair
  simp only [numeralRename,zRelabel] at pp
  have parent := moveParent P.V P.R s q both row.parent
  simp only [ordinaryRename,singletonTypeKey,rawConsRename,termRename,zRelabel] at parent
  let a := singletonTypeKey (ty.relabel q)
  let d : OTerm γ := numeral 2
  let R := selectedMeasure P.R
  have paid : OrdinaryOwnInputs P.V R s body Ξ (p.relabel q) d z d z
      later lt la (h.relabel q) a :=
    ⟨after,args,selfWeak d,selfWeak z,hd,parent.valid,parent.measured,pp⟩
  rw [formulaRelabelComposition j g Q]
  simp only [Q,graphRename,ordinaryRename,singletonTypeKey,rawConsRename,termRename,zRelabel]
  exact exact_OpenSelectedGrammarOrdinaryScratch P.V R s body γ Ξ (p.relabel q) d z d z
    later lt la (vertices.relabel q) (h.relabel q) a paid parent.held

theorem exact_OpenCoverOrdinarySingletonTypeScratch : ExactOpenCoverOrdinarySingletonTypeScratch := by
  intro V TV M A B T s body α Γ h ty p vertices ctx result row inK
  let C := singletonTypeArgs A
  let L := lambdaLexicalBase s B T
  let P := lexicalFittedPrograms s V TV M C B T
  let a := singletonTypeKey ty
  have head := exact_OpenCoverHeadFittedWindow false s (numberedTypeBase s L) T
    body α Γ ctx h result [a] rfl row.typed
  have cut := exact_OpenCoverOrdinaryMeasureCut (numberedMeasureBase M C) C body α Γ h a p row.parent.measured
  have argument := exact_OpenCoverSingletonTypeArgument A body α Γ ty
  have bump := exact_OpenOrdinaryBumpFromArgument C h a p singletonMeasureCode cut argument
  have parentPair := exact_OpenCoverLambdaBumpPair body α Γ p singletonMeasureCode (numeral 2) z
    singletonCodePair bump
  exact atObservedScopes P s h ty p vertices ctx result row head inK parentPair

#print axioms exact_OpenCoverOrdinarySingletonTypeScratch

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSingletonTypeArgumentScratchProof
