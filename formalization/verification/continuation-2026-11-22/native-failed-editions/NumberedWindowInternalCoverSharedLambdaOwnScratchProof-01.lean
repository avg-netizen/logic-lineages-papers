module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedOwnScratchTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedLambdaSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedLambdaMeasureProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaDerivedOwnInputSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarLambdaOwnScratchProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarLambdaOwnTermPartProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthObservationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedLambdaOwnScratchProof
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
open NumberedWindowInternalSparsePassWindowSyntaxProof (windowRename)
open NumberedWindowInternalCoverSelectedGrammarWidthObservationProof (observationCases)
open NumberedWindowInternalCoverSelectedGrammarLambdaOwnScratchProof (exact_OpenSelectedGrammarLambdaMeasuredScratch)
open NumberedWindowInternalCoverSelectedGrammarLambdaOwnTermPartProof (lambdaRename)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (headsTerm typesTerm)
open NumberedWindowInternalChosenAuxMeasureCombineOpenTargets (codePair)
open NumberedWindowInternalCoverLambdaLayerTargets (lambdaTerm)
open NumberedWindowInternalCoverLambdaDerivedOwnInputSyntaxProof (specializeIH ihRename)
open NumberedWindowInternalCoverSharedRecursionTargets (sharedSyntax sharedMeasure)
open NumberedWindowInternalCoverSharedLambdaSyntaxProof (exact_OpenCoverSharedLambdaSyntaxParent)
open NumberedWindowInternalCoverSharedLambdaMeasureProof (exact_OpenCoverSharedLambdaMeasureParent)
open NumberedWindowInternalCoverSharedOwnScratchTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem moveInputs (V T M : Program 1) (W : Program 3) (s : Settings)
    (p vertices ctx bodyTy ty q : OTerm α) {β : Type} {Δ : List (Formula β)} (j : α → β) (keep : ∀ f ∈ Γ, f.relabel j ∈ Δ)
    (paid : LambdaInputs V T M W s body Γ p vertices ctx bodyTy ty q) :
    LambdaInputs V T M W s body Δ (p.relabel j) (vertices.relabel j) (ctx.relabel j)
      (bodyTy.relabel j) (ty.relabel j) (q.relabel j) := by
  constructor
  · have actual := renameInto paid.valid j Δ keep
    simpa only [unaryRename,lambdaRename,sucRelabel,zRelabel] using actual
  · have actual := renameInto paid.measured j Δ keep
    simpa only [unaryRename,lambdaRename] using actual
  · have actual := renameInto paid.typedBody j Δ keep
    simpa only [windowRename] using actual
  · have actual := renameInto paid.bodyIH j Δ keep
    simpa only [ihRename] using actual
  · have actual := renameInto paid.typeMember j Δ keep
    simpa only [graphRename,typesTerm,numeralRename] using actual
  · have actual := renameInto paid.held j Δ keep
    simpa only [unaryRename,lambdaRename] using actual

private theorem fromCoordinates (V T M : Program 1) (W : Program 3) (s : Settings)
    (p mc d width vertices ctx bodyTy ty q : OTerm α)
    (paid : LambdaInputs V T M W s body Γ p vertices ctx bodyTy ty q)
    (childValid : Nonempty (Derivation body Γ (unary (sharedSyntax V T) (suc z) q)))
    (childMeasure : Nonempty (Derivation body Γ (unary (sharedMeasure M) mc q)))
    (childPair : Nonempty (Derivation body Γ (codePair mc d width)))
    (parentPair : Nonempty (Derivation body Γ (codePair p (suc d) width))) :
    Nonempty (Derivation body Γ (memberGraph vertices (lambdaTerm ty q))) := by
  apply observationCases d (headsTerm s α) (typesTerm s α) width _
  intro β j Δ state terms args keep child
  rw [graphRename,lambdaRename]
  simp only [headsTerm,typesTerm,numeralRename] at child
  have paid' := moveInputs V T M W s p vertices ctx bodyTy ty q j keep paid
  have valid' := renameInto childValid j Δ keep
  have measure' := renameInto childMeasure j Δ keep
  have childPair' := renameInto childPair j Δ keep
  have parentPair' := renameInto parentPair j Δ keep
  simp only [unaryRename,sucRelabel,zRelabel] at valid'
  simp only [unaryRename] at measure'
  simp only [codePair,programRename,binaryInputsRename,sucRelabel] at childPair' parentPair'
  have ih := specializeIH W (sharedCover V T M) s (ctx.relabel j) (bodyTy.relabel j) (q.relabel j) terms paid'.bodyIH
  exact exact_OpenSelectedGrammarLambdaMeasuredScratch (sharedSyntax V T) (sharedMeasure M) W s
    body β Δ (p.relabel j) (mc.relabel j) (d.relabel j) (width.relabel j) state terms args
    (vertices.relabel j) (ctx.relabel j) (bodyTy.relabel j) (ty.relabel j) (q.relabel j)
    paid'.typedBody ih child valid' measure' childPair' paid'.typeMember paid'.valid paid'.measured parentPair' paid'.held


theorem exact_OpenCoverSharedLambdaOwnScratch : ExactOpenCoverSharedLambdaOwnScratch := by
  intro V TV M W s body α Γ p vertices ctx bodyTy ty q paid
  obtain ⟨syntax⟩ := exact_OpenCoverSharedLambdaSyntaxParent V TV body α Γ ty q paid.valid
  have childValid := Nonempty.intro (Derivation.conjunctionRight syntax)
  apply exact_OpenCoverSharedLambdaMeasureParent M body α Γ ty q p _ paid.measured
  intro β j Δ old mc d width keep row
  rw [graphRename,lambdaRename]
  have paid' := moveInputs V TV M W s p vertices ctx bodyTy ty q j keep paid
  have valid' := renameInto childValid j Δ keep
  simp only [unaryRename,sucRelabel,zRelabel] at valid'
  exact fromCoordinates V TV M W s (p.relabel j) mc d width (vertices.relabel j)
    (ctx.relabel j) (bodyTy.relabel j) (ty.relabel j) (q.relabel j) paid'
    valid' row.child.selected row.child.coordinates row.parentPair

#print axioms exact_OpenCoverSharedLambdaOwnScratch

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedLambdaOwnScratchProof
