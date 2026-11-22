module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRestrictedLambdaFragmentTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaAuxFragmentOwnTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverRestrictedLambdaFragmentOwnTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalCoverLambdaLayerTargets (lambdaTerm)
open NumberedWindowInternalCoverRefinedInductionDispatchTargets (ParentRow)
open NumberedWindowInternalCoverLambdaBoundCoherenceTargets (lexicalFittedPrograms)
open NumberedWindowInternalCoverRestrictedLambdaFragmentTargets (lambdaFragmentBase)

/-- The positive physical restricted W′ parent supplies its own fragment
guard. The original same-program bounded parent premise stays in ParentRow. -/
def ExactOpenCoverRestrictedLambdaFragmentOwnScratch : Prop :=
  ∀ (V TV M A : Program 1) (B : Program 2) (T : Program 1) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (dom q p vertices ctx result : OTerm α),
    ParentRow (lexicalFittedPrograms s V TV M A (lambdaFragmentBase B) T) s body Γ
      (lambdaTerm dom q) p vertices ctx result →
    Nonempty (Derivation body Γ (memberGraph vertices (lambdaTerm dom q)))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverRestrictedLambdaFragmentOwnTargets
