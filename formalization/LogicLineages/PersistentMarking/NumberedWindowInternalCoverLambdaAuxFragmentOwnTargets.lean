module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxFragmentInductionTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaBoundCoherenceTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaAuxFragmentOwnTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalCoverAuxFragmentGuardTargets (fragmentGuard)
open NumberedWindowInternalCoverLambdaLayerTargets (lambdaTerm)
open NumberedWindowInternalCoverRefinedInductionDispatchTargets (ParentRow)
open NumberedWindowInternalCoverLambdaBoundCoherenceTargets (lexicalFittedPrograms)

/-- A genuine lexical lambda parent and its actual bounded own-key
premise, with selected fragment acceptance on the raw immediate body. -/
def ExactOpenCoverLambdaAuxFragmentOwnScratch : Prop :=
  ∀ (V TV M A : Program 1) (B : Program 2) (T : Program 1) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (dom q p vertices ctx result : OTerm α),
    ParentRow (lexicalFittedPrograms s V TV M A B T) s body Γ
      (lambdaTerm dom q) p vertices ctx result →
    Nonempty (Derivation body Γ (unary fragmentGuard (suc z) q)) →
    Nonempty (Derivation body Γ (memberGraph vertices (lambdaTerm dom q)))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaAuxFragmentOwnTargets
