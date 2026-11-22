module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNumberedOwnTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNumberedOwnStageProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarCrossBoundProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNumberedOwnBoundsProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb bindEmbedding liftBind varBind)
open ID1Completion.InternalAdditionLawsProof (impSubst)
open NumberedWindowInternalSparsePassWindowSyntaxProof (memberSubst)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalCoverSelectedGrammarWidthTargets (observed)
open NumberedWindowInternalCoverSelectedGrammarCrossBoundProof (exact_OpenSelectedGrammarCrossBound)
open NumberedWindowInternalCoverSelectedGrammarNumberedOwnStageProof (exact_OpenSelectedGrammarNumberedFromPredecessor)
open NumberedWindowInternalCoverSelectedGrammarNumberedOwnTargets

private theorem bring {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (d H K M da Ma state terms args key prev prevTerms prevArgs : OTerm α)
    (paid : BoundedNumberedArgs body Γ d H K M da Ma state terms args key)
    (before : Nonempty (Derivation body Γ (observed d H K M prev prevTerms prevArgs))) :
    Nonempty (Derivation body Γ (memberGraph prevArgs key)) := by
  obtain ⟨inc⟩ := exact_OpenSelectedGrammarCrossBound body α Γ da d H K Ma M
    state terms args prev prevTerms prevArgs paid.depth paid.width paid.scope before
  have law : Derivation body Γ ((memberGraph args key).imp (memberGraph prevArgs key)) := by
    simpa only [instantiate,bindEmbedding,impSubst,memberSubst,liftBind,varBind] using
      (Derivation.universalElimination (emb key) (Derivation.conjunctionRight inc))
  obtain ⟨hit⟩ := paid.hit
  exact ⟨Derivation.implicationElimination law hit⟩

theorem exact_OpenSelectedGrammarNumberedAtBounds : ExactOpenSelectedGrammarNumberedAtBounds := by
  intro body α Γ d H K M dl Ml lState lTerms lArgs dr Mr rState rTerms rArgs
    prev prevTerms prevArgs next out nextArgs h ty k l r left right before after ht hy hk
  have hl := bring d H K M dl Ml lState lTerms lArgs l prev prevTerms prevArgs left before
  have hr := bring d H K M dr Mr rState rTerms rArgs r prev prevTerms prevArgs right before
  exact exact_OpenSelectedGrammarNumberedFromPredecessor body α Γ d H K M
    prev prevTerms prevArgs next out nextArgs h ty k l r before after ht hy hk hl hr

#print axioms exact_OpenSelectedGrammarNumberedAtBounds

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNumberedOwnBoundsProof
