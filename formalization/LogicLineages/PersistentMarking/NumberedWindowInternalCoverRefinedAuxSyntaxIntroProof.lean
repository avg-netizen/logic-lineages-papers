module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedAuxSyntaxIntroTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedAuxSyntaxIntroRowProof
import LogicLineages.PersistentMarking.NumberedWindowInternalScratchMemoThinSuccessorProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureObservedSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedAuxSyntaxIntroProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseFieldParser (scratchTable)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (auxiliaryRename)
open NumberedWindowInternalChosenAuxMeasureMemoTargets (memoPrior)
open NumberedWindowInternalChosenAuxMeasureObservedSyntaxProof (priorRename)
open NumberedWindowInternalAuxExchangeMemoOpenTableTargets (tableAt)
open NumberedWindowInternalAuxMeasureOpenDataProof (projection)
open NumberedWindowInternalScratchMemoThinSuccessorProof (exact_OpenSelectedMemoSuccessor)
open NumberedWindowInternalCoverRefinedSharedSyntaxTargets (refinedUpdate refinedSyntax refinedAuxChildren)
open NumberedWindowInternalCoverRefinedAuxSyntaxIntroRowProof (exact_OpenCoverRefinedAuxSyntaxIntroRow)
open NumberedWindowInternalCoverRefinedAuxSyntaxIntroTargets

theorem exact_OpenCoverRefinedAuxSyntaxIntro : ExactOpenCoverRefinedAuxSyntaxIntro := by
  intro V TV body α Γ dom cod fn arg child
  let R : Program 4 := refinedUpdate V TV
  let Goal : Formula α := unary (refinedSyntax V TV) (suc z) (auxiliaryTerm dom cod fn arg)
  apply programCases (scratchTable (constantZero 2) R) ![memoPrior dom cod fn arg,z,z] Goal
  intro β j Δ old keep table
  simp only [tripleInputsRename,priorRename,zRelabel] at table
  let d := dom.relabel j
  let c := cod.relabel j
  let f := fn.relabel j
  let a := arg.relabel j
  have actual := renameInto child j Δ keep
  simp only [refinedAuxChildren,conjunctionRename,unaryRename,sucRelabel,zRelabel] at actual
  have row := exact_OpenCoverRefinedAuxSyntaxIntroRow V TV body β Δ d c f a old actual table
  have installed := exact_OpenSelectedMemoSuccessor R body β Δ (suc z) (memoPrior d c f a) old table row
  change Nonempty (Derivation body Δ ((unary (refinedSyntax V TV) (suc z) (auxiliaryTerm dom cod fn arg)).relabel j))
  simp only [unaryRename,sucRelabel,zRelabel,auxiliaryRename]
  exact (projection R (suc z) (auxiliaryTerm d c f a)).mpr installed

#print axioms exact_OpenCoverRefinedAuxSyntaxIntro

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedAuxSyntaxIntroProof
