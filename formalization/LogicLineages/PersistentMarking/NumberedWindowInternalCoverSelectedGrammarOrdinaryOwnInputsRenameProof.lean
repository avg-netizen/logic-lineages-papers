module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnTermPartProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnInputsRenameProof
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
open NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnTermPartProof (ordinaryRename)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α β : Type} {Γ : List (Formula α)} {Δ : List (Formula β)}

theorem inputsRename (V Measure : Program 1) (s : Settings)
    (m d M da Ma aState aTerms aArgs h a : OTerm α)
    (j : α → β) (keep : ∀ p ∈ Γ, p.relabel j ∈ Δ)
    (paid : OrdinaryOwnInputs V Measure s body Γ m d M da Ma aState aTerms aArgs h a) :
    OrdinaryOwnInputs V Measure s body Δ (m.relabel j) (d.relabel j) (M.relabel j)
      (da.relabel j) (Ma.relabel j) (aState.relabel j) (aTerms.relabel j) (aArgs.relabel j)
      (h.relabel j) (a.relabel j) := by
  constructor
  · have actual := renameInto paid.argumentScope j Δ keep
    simpa only [observedRename,headsTerm,typesTerm,numeralRename] using actual
  · have actual := renameInto paid.argumentHit j Δ keep
    simpa only [graphRename] using actual
  · have actual := renameInto paid.argumentDepth j Δ keep
    simpa only [orderRename,sucRelabel] using actual
  · have actual := renameInto paid.argumentWidth j Δ keep
    simpa only [orderRename,sucRelabel] using actual
  · have actual := renameInto paid.headHit j Δ keep
    simpa only [graphRename,headsTerm,numeralRename] using actual
  · have actual := renameInto paid.validity j Δ keep
    simpa only [unaryRename,sucRelabel,zRelabel,ordinaryRename] using actual
  · have actual := renameInto paid.measurement j Δ keep
    simpa only [unaryRename,ordinaryRename] using actual
  · have actual := renameInto paid.parentPair j Δ keep
    simpa only [measurePair,programRename,binaryInputsRename,sucRelabel] using actual

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnInputsRenameProof
