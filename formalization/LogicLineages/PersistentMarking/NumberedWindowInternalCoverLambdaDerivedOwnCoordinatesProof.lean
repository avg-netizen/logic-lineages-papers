module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaDerivedOwnTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaDerivedOwnInputSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarLambdaOwnScratchProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarLambdaOwnTermPartProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthObservationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaDerivedOwnCoordinatesProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalCoverSelectedGrammarWidthObservationProof (observationCases)
open NumberedWindowInternalCoverSelectedGrammarLambdaOwnScratchProof (exact_OpenSelectedGrammarLambdaMeasuredScratch)
open NumberedWindowInternalCoverSelectedGrammarLambdaOwnTermPartProof (lambdaRename)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (headsTerm typesTerm)
open NumberedWindowInternalChosenAuxMeasureCombineOpenTargets (codePair)
open NumberedWindowInternalCoverLambdaLayerTargets (lambdaTerm)
open NumberedWindowInternalCoverLambdaSyntaxRowTargets (lambdaSyntax)
open NumberedWindowInternalCoverLambdaMeasureRowTargets (lambdaMeasure)
open NumberedWindowInternalCoverLambdaDerivedOwnInputSyntaxProof (specializeIH inputsRename)
open NumberedWindowInternalCoverLambdaDerivedOwnTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem fromCoordinates (V T M : Program 1) (W : Program 3) (s : Settings)
    (p mc d width vertices ctx bodyTy ty q : OTerm α)
    (paid : Inputs V T M W s body Γ p vertices ctx bodyTy ty q)
    (childValid : Nonempty (Derivation body Γ (unary (lambdaSyntax V T) (suc z) q)))
    (childMeasure : Nonempty (Derivation body Γ (unary (lambdaMeasure M) mc q)))
    (childPair : Nonempty (Derivation body Γ (codePair mc d width)))
    (parentPair : Nonempty (Derivation body Γ (codePair p (suc d) width))) :
    Nonempty (Derivation body Γ (memberGraph vertices (lambdaTerm ty q))) := by
  apply observationCases d (headsTerm s α) (typesTerm s α) width _
  intro β j Δ state terms args keep child
  rw [graphRename,lambdaRename]
  simp only [headsTerm,typesTerm,numeralRename] at child
  have paid' := inputsRename V T M W s p vertices ctx bodyTy ty q j keep paid
  have valid' := renameInto childValid j Δ keep
  have measure' := renameInto childMeasure j Δ keep
  have childPair' := renameInto childPair j Δ keep
  have parentPair' := renameInto parentPair j Δ keep
  simp only [unaryRename,sucRelabel,zRelabel] at valid'
  simp only [unaryRename] at measure'
  simp only [codePair,programRename,binaryInputsRename,sucRelabel] at childPair' parentPair'
  have ih := specializeIH W (lambdaCover V T M) s (ctx.relabel j) (bodyTy.relabel j) (q.relabel j) terms paid'.localIH
  exact exact_OpenSelectedGrammarLambdaMeasuredScratch (lambdaSyntax V T) (lambdaMeasure M) W s
    body β Δ (p.relabel j) (mc.relabel j) (d.relabel j) (width.relabel j) state terms args
    (vertices.relabel j) (ctx.relabel j) (bodyTy.relabel j) (ty.relabel j) (q.relabel j)
    paid'.typed ih child valid' measure' childPair' paid'.typeMember paid'.valid paid'.measured parentPair' paid'.held

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaDerivedOwnCoordinatesProof
