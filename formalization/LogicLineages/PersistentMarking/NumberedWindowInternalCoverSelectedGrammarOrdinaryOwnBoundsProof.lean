module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnStageProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarCrossBoundProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnBoundsProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalTagArithmeticSyntaxProof (emb bindEmbedding liftBind varBind)
open ID1Completion.InternalAdditionLawsProof (impSubst)
open NumberedWindowInternalSparsePassWindowSyntaxProof (memberSubst)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalCoverSelectedGrammarCrossBoundProof (exact_OpenSelectedGrammarCrossBound)
open NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnStageProof (exact_OpenSelectedGrammarOrdinaryFromPredecessor)
open NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnTargets

theorem exact_OpenSelectedGrammarOrdinaryAtBounds : ExactOpenSelectedGrammarOrdinaryAtBounds := by
  intro body α Γ d H K M da Ma aState aTerms aArgs
    prev prevTerms prevArgs next out args h a child hit dep wid before after ht
  obtain ⟨inc⟩ := exact_OpenSelectedGrammarCrossBound body α Γ da d H K Ma M
    aState aTerms aArgs prev prevTerms prevArgs dep wid child before
  have law : Derivation body Γ ((memberGraph aArgs a).imp (memberGraph prevArgs a)) := by
    simpa only [instantiate,bindEmbedding,impSubst,memberSubst,liftBind,varBind] using
      (Derivation.universalElimination (emb a) (Derivation.conjunctionRight inc))
  obtain ⟨hit⟩ := hit
  exact exact_OpenSelectedGrammarOrdinaryFromPredecessor body α Γ d H K M
    prev prevTerms prevArgs next out args h a before after ht
    ⟨Derivation.implicationElimination law hit⟩

#print axioms exact_OpenSelectedGrammarOrdinaryAtBounds

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnBoundsProof
