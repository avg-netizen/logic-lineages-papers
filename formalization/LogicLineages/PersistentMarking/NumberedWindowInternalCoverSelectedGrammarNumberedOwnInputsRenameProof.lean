module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNumberedOwnTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedLayerOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNumberedOwnInputsRenameProof
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
open NumberedWindowInternalCoverNumberedLayerOpenDataProof (numberedRename)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalCoverSelectedGrammarNumberedOwnTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α β : Type} {Γ : List (Formula α)} {Δ : List (Formula β)}

private theorem boundedRename (d H K M da Ma state terms args key : OTerm α)
    (j : α → β) (keep : ∀ p ∈ Γ, p.relabel j ∈ Δ)
    (paid : BoundedNumberedArgs body Γ d H K M da Ma state terms args key) :
    BoundedNumberedArgs body Δ (d.relabel j) (H.relabel j) (K.relabel j) (M.relabel j)
      (da.relabel j) (Ma.relabel j) (state.relabel j) (terms.relabel j) (args.relabel j) (key.relabel j) := by
  constructor
  · have actual := renameInto paid.scope j Δ keep
    simpa only [observedRename] using actual
  · have actual := renameInto paid.hit j Δ keep
    simpa only [graphRename] using actual
  · have actual := renameInto paid.depth j Δ keep
    simpa only [orderRename,sucRelabel] using actual
  · have actual := renameInto paid.width j Δ keep
    simpa only [orderRename,sucRelabel] using actual

theorem inputsRename (V Measure : Program 1) (s : Settings)
    (m d M dl Ml lState lTerms lArgs dr Mr rState rTerms rArgs h ty k l r : OTerm α)
    (j : α → β) (keep : ∀ p ∈ Γ, p.relabel j ∈ Δ)
    (paid : NumberedOwnInputs V Measure s body Γ m d M dl Ml lState lTerms lArgs
      dr Mr rState rTerms rArgs h ty k l r) :
    NumberedOwnInputs V Measure s body Δ (m.relabel j) (d.relabel j) (M.relabel j)
      (dl.relabel j) (Ml.relabel j) (lState.relabel j) (lTerms.relabel j) (lArgs.relabel j)
      (dr.relabel j) (Mr.relabel j) (rState.relabel j) (rTerms.relabel j) (rArgs.relabel j)
      (h.relabel j) (ty.relabel j) (k.relabel j) (l.relabel j) (r.relabel j) := by
  constructor
  · have actual := boundedRename d (headsTerm s α) (typesTerm s α) M dl Ml lState lTerms lArgs l j keep paid.prefix
    simpa only [headsTerm,typesTerm,numeralRename] using actual
  · have actual := boundedRename d (headsTerm s α) (typesTerm s α) M dr Mr rState rTerms rArgs r j keep paid.suffix
    simpa only [headsTerm,typesTerm,numeralRename] using actual
  · have actual := renameInto paid.headHit j Δ keep
    simpa only [graphRename,headsTerm,numeralRename] using actual
  · have actual := renameInto paid.typeHit j Δ keep
    simpa only [graphRename,typesTerm,numeralRename] using actual
  · have actual := renameInto paid.idBound j Δ keep
    simpa only [orderRename,sucRelabel] using actual
  · have actual := renameInto paid.validity j Δ keep
    simpa only [unaryRename,sucRelabel,zRelabel,numberedRename] using actual
  · have actual := renameInto paid.measurement j Δ keep
    simpa only [unaryRename,numberedRename] using actual
  · have actual := renameInto paid.parentPair j Δ keep
    simpa only [measurePair,programRename,binaryInputsRename,sucRelabel] using actual

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNumberedOwnInputsRenameProof
