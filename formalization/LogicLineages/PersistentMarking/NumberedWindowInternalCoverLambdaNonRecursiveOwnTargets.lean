module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverFittedBaseTapeForwardTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaBoundCoherenceTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaNonRecursiveOwnTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseRawFunctionFrame (termShape)
open NumberedWindowInternalCoverSelectedValidityTargets (header)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalCoverLambdaLayerTargets (lambdaTerm)
open NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnTargets (ordinaryKey)
open NumberedWindowInternalCoverNumberedLayerTargets (numberedTerm)
open NumberedWindowInternalCoverRefinedInductionDispatchTargets (ParentRow)
open NumberedWindowInternalCoverLambdaBoundCoherenceTargets (lexicalFittedPrograms)

def ExactOpenCoverLambdaNonRecursiveOwnScratch : Prop :=
  ∀ (V TV M A : Program 1) (B : Program 2) (T : Program 1) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (dom childPrior p vertices ctx result : OTerm α),
    ParentRow (lexicalFittedPrograms s V TV M A B T) s body Γ
      (lambdaTerm dom (suc childPrior)) p vertices ctx result →
    Nonempty (Derivation body Γ (unary (header 2 2) z (suc childPrior))) →
    Nonempty (Derivation body Γ (unary termShape z (suc childPrior))) →
    Nonempty (Derivation body Γ (memberGraph vertices (lambdaTerm dom (suc childPrior))))

def ExactOpenCoverLambdaOrdinaryBodyOwnScratch : Prop :=
  ∀ (V TV M A : Program 1) (B : Program 2) (T : Program 1) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (dom h a p vertices ctx result : OTerm α),
    ParentRow (lexicalFittedPrograms s V TV M A B T) s body Γ
      (lambdaTerm dom (ordinaryKey h a)) p vertices ctx result →
    Nonempty (Derivation body Γ (memberGraph vertices (lambdaTerm dom (ordinaryKey h a))))

def ExactOpenCoverLambdaNumberedBodyOwnScratch : Prop :=
  ∀ (V TV M A : Program 1) (B : Program 2) (T : Program 1) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (dom h ty k l r p vertices ctx result : OTerm α),
    ParentRow (lexicalFittedPrograms s V TV M A B T) s body Γ
      (lambdaTerm dom (numberedTerm h ty k l r)) p vertices ctx result →
    Nonempty (Derivation body Γ (memberGraph vertices (lambdaTerm dom (numberedTerm h ty k l r))))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaNonRecursiveOwnTargets
