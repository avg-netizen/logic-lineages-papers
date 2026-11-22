module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarAuxScratchTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarAuxScratchInputsRenameProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open ID1Completion.InternalOriginalOrderSyntaxProof (orderRename)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open NumberedWindowScalarAlgorithm (Settings)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalFactoredAuxOwnCoverTargets (headsTerm typesTerm measurePair)
open NumberedWindowInternalCoverSelectedGrammarWidthSyntaxProof (observedRename)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (auxiliaryRename)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalCoverSelectedGrammarAuxScratchTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α β : Type} {Γ : List (Formula α)} {Δ : List (Formula β)}

theorem inputsRename (V Measure : Program 1) (s : Settings)
    (m d maxNumeral df mf da ma fState fTerms fArgs aState aTerms aArgs dom cod fn arg : OTerm α)
    (j : α → β) (keep : ∀ p ∈ Γ, p.relabel j ∈ Δ)
    (paid : AuxParentInputs V Measure s body Γ m d maxNumeral df mf da ma
      fState fTerms fArgs aState aTerms aArgs dom cod fn arg) :
    AuxParentInputs V Measure s body Δ (m.relabel j) (d.relabel j) (maxNumeral.relabel j)
      (df.relabel j) (mf.relabel j) (da.relabel j) (ma.relabel j)
      (fState.relabel j) (fTerms.relabel j) (fArgs.relabel j) (aState.relabel j) (aTerms.relabel j) (aArgs.relabel j)
      (dom.relabel j) (cod.relabel j) (fn.relabel j) (arg.relabel j) := by
  constructor
  · have actual := renameInto paid.functionReport j Δ keep
    rw [observedRename] at actual
    simpa only [headsTerm,typesTerm,numeralRename] using actual
  · have actual := renameInto paid.argumentReport j Δ keep
    rw [observedRename] at actual
    simpa only [headsTerm,typesTerm,numeralRename] using actual
  · have actual := renameInto paid.functionMember j Δ keep
    rw [graphRename] at actual
    exact actual
  · have actual := renameInto paid.argumentMember j Δ keep
    rw [graphRename] at actual
    exact actual
  · have actual := renameInto paid.functionDepth j Δ keep
    rw [orderRename,sucRelabel] at actual
    exact actual
  · have actual := renameInto paid.functionWidth j Δ keep
    rw [orderRename,sucRelabel] at actual
    exact actual
  · have actual := renameInto paid.argumentDepth j Δ keep
    rw [orderRename,sucRelabel] at actual
    exact actual
  · have actual := renameInto paid.argumentWidth j Δ keep
    rw [orderRename,sucRelabel] at actual
    exact actual
  · have actual := renameInto paid.domainMember j Δ keep
    rw [graphRename] at actual
    simpa only [typesTerm,numeralRename] using actual
  · have actual := renameInto paid.codomainMember j Δ keep
    rw [graphRename] at actual
    simpa only [typesTerm,numeralRename] using actual
  · have actual := renameInto paid.validity j Δ keep
    simpa only [unaryRename,sucRelabel,zRelabel,auxiliaryRename] using actual
  · have actual := renameInto paid.measure j Δ keep
    simpa only [unaryRename,auxiliaryRename] using actual
  · have actual := renameInto paid.measureCode j Δ keep
    simpa only [measurePair,programRename,binaryInputsRename,sucRelabel] using actual

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarAuxScratchInputsRenameProof
