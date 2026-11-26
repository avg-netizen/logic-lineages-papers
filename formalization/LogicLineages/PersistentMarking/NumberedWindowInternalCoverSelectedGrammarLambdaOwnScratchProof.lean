module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarLambdaOwnTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarLambdaOwnBoundsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarLambdaOwnTermPartProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOptionOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthObservationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceInversionSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarLambdaOwnScratchProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (valueUnique headTransport programRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (trans addZero addSucc congSuc)
open ID1Completion.InternalOriginalOrderProof (actualOriginalOrderIntroduction)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalSourceInversionSupportProof (onEquality)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalSparseCoverScratch (scratchVertices)
open NumberedWindowInternalCoverLambdaLayerTargets (lambdaTerm)
open NumberedWindowInternalCoverSelectedGrammarLambdaOwnTermPartProof (lambdaRename)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (headsTerm typesTerm measurePair)
open NumberedWindowInternalCoverSelectedGrammarWidthObservationProof (observationCases)
open NumberedWindowInternalCoverSelectedGrammarWidthSyntaxProof (observedRename)
open NumberedWindowInternalCoverSelectedGrammarAuxScratchTargets (selectedCover)
open NumberedWindowInternalCoverSelectedGrammarOptionOpenProof
  (exact_ObservedSelectedTerms exact_OpenSelectedGrammarFactoredScratch)
open NumberedWindowInternalCoverSelectedGrammarLambdaOwnTargets
open NumberedWindowInternalCoverSelectedGrammarLambdaOwnBoundsProof (exact_OpenSelectedGrammarLambdaAtBounds)

attribute [local irreducible] programGraph

private theorem weakSelf {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (n : OTerm α) : Nonempty (Derivation body Γ (ltF n (suc n))) := by
  apply actualOriginalOrderIntroduction body α Γ n (suc n) z
  rw [onEquality]
  exact ⟨trans (addSucc n z) (congSuc (addZero n))⟩

theorem exact_OpenSelectedGrammarLambdaMeasuredScratch : ExactOpenSelectedGrammarLambdaMeasuredScratch := by
  intro V Measure W s body α Γ m mc d M childState childTerms childArgs vertices ctx bodyTy ty q
    typed ih child childValid childMeasure childPair ht valid measured pair held
  let H := headsTerm s α
  let K := typesTerm s α
  have childTermsGraph := exact_ObservedSelectedTerms d H K M childState childTerms childArgs child
  have childInstalled := exact_OpenSelectedGrammarFactoredScratch V Measure s mc d M childTerms q
    childValid childMeasure childPair childTermsGraph
  obtain ⟨typed⟩ := typed
  obtain ⟨ih⟩ := ih
  obtain ⟨actualChildScratch⟩ := childInstalled.2
  have childHit := Nonempty.intro
    (Derivation.implicationElimination (Derivation.implicationElimination ih typed) actualChildScratch)
  apply observationCases (suc d) H K M _
  intro β j Δ next out args keep after
  rw [graphRename,lambdaRename]
  simp only [H,K,headsTerm,typesTerm,sucRelabel,numeralRename] at after
  have child' := renameInto child j Δ keep
  simp only [observedRename,headsTerm,typesTerm,numeralRename] at child'
  have hit' := renameInto childHit j Δ keep
  rw [graphRename] at hit'
  have ht' := renameInto ht j Δ keep
  have valid' := renameInto valid j Δ keep
  have measured' := renameInto measured j Δ keep
  have pair' := renameInto pair j Δ keep
  have held' := renameInto held j Δ keep
  simp only [graphRename,typesTerm,numeralRename] at ht'
  simp only [unaryRename,lambdaRename,sucRelabel,zRelabel] at valid'
  simp only [unaryRename,lambdaRename] at measured' held'
  simp only [measurePair,programRename,binaryInputsRename,sucRelabel] at pair'
  let H' := headsTerm s β
  let K' := typesTerm s β
  let key := lambdaTerm (ty.relabel j) (q.relabel j)
  have hit := exact_OpenSelectedGrammarLambdaAtBounds body β Δ (d.relabel j) H' K' (M.relabel j)
    (d.relabel j) (M.relabel j) (childState.relabel j) (childTerms.relabel j) (childArgs.relabel j)
    (childState.relabel j) (childTerms.relabel j) (childArgs.relabel j) next out args
    (ty.relabel j) (q.relabel j) child' hit' (weakSelf (d.relabel j)) (weakSelf (M.relabel j))
    child' after ht'
  have terms := exact_ObservedSelectedTerms (suc (d.relabel j)) H' K' (M.relabel j) next out args after
  have installed := exact_OpenSelectedGrammarFactoredScratch V Measure s (m.relabel j)
    (suc (d.relabel j)) (M.relabel j) out key valid' measured' pair' terms
  let P := scratchVertices (selectedCover V Measure) s
  have eq := valueUnique P out (vertices.relabel j) ![key] installed.2 held'
  exact headTransport scratchMember (suc z) out (vertices.relabel j) ![key] eq hit

#print axioms exact_OpenSelectedGrammarLambdaMeasuredScratch

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarLambdaOwnScratchProof
