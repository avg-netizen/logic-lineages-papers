module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarLambdaOwnTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarLambdaOwnStageProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarCrossBoundProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarLambdaOwnBoundsProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalTagArithmeticSyntaxProof (emb bindEmbedding liftBind varBind)
open ID1Completion.InternalAdditionLawsProof (impSubst)
open NumberedWindowInternalSparsePassWindowSyntaxProof (memberSubst)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalCoverSelectedGrammarCrossBoundProof (exact_OpenSelectedGrammarCrossBound)
open NumberedWindowInternalCoverSelectedGrammarLambdaOwnStageProof (exact_OpenSelectedGrammarLambdaFromPredecessor)
open NumberedWindowInternalCoverSelectedGrammarLambdaOwnTargets

theorem exact_OpenSelectedGrammarLambdaAtBounds : ExactOpenSelectedGrammarLambdaAtBounds := by
  intro body α Γ d H K M childD childW childState childTerms childArgs
    prev prevTerms prevArgs next out args ty q child hit dep wid before after ht
  obtain ⟨inc⟩ := exact_OpenSelectedGrammarCrossBound body α Γ childD d H K childW M
    childState childTerms childArgs prev prevTerms prevArgs dep wid child before
  have law : Derivation body Γ ((memberGraph childTerms q).imp (memberGraph prevTerms q)) := by
    simpa only [instantiate,bindEmbedding,impSubst,memberSubst,liftBind,varBind] using
      (Derivation.universalElimination (emb q) (Derivation.conjunctionLeft inc))
  obtain ⟨hit⟩ := hit
  exact exact_OpenSelectedGrammarLambdaFromPredecessor body α Γ d H K M
    prev prevTerms prevArgs next out args ty q before after ht
    ⟨Derivation.implicationElimination law hit⟩

#print axioms exact_OpenSelectedGrammarLambdaAtBounds

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarLambdaOwnBoundsProof
