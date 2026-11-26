module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverGuardedOrdinaryListTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverGuardedNumberedListTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalCoverNumberedLayerTargets (numberedTerm)
open NumberedWindowInternalCoverRefinedInductionDispatchTargets (ParentRow)
open NumberedWindowInternalCoverLambdaBoundCoherenceTargets (lexicalFittedPrograms)
open NumberedWindowInternalCoverArgumentMemoTargets (argumentMeasure)
open NumberedWindowInternalCoverArgumentGuardTargets (argumentReject)
open NumberedWindowInternalCoverArgumentGrammarInductionTargets (HeadProvider argumentExists)
open NumberedWindowInternalCoverTypeOnlyArgumentListTargets (typeOnlyHeadGuard)
open NumberedWindowInternalCoverTypeLeafMeasureTargets (typeLeafSharedMeasure)

def ExactOpenCoverMeasuredNumberedListScratch : Prop :=
  ∀ (V TV M F : Program 1) (B : Program 2) (T : Program 1) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (h ty k l r p vertices ctx result : OTerm α),
    ParentRow (lexicalFittedPrograms s V TV M (argumentMeasure F) B T) s body Γ
      (numberedTerm h ty k l r) p vertices ctx result →
    Nonempty (Derivation body Γ (argumentExists F s l)) →
    Nonempty (Derivation body Γ (argumentExists F s r)) →
    Nonempty (Derivation body Γ (memberGraph vertices (numberedTerm h ty k l r)))

def ExactOpenCoverGuardedNumberedListScratch : Prop :=
  ∀ (V TV M F G : Program 1) (B : Program 2) (T : Program 1) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (h ty k l r p vertices ctx result : OTerm α),
    ParentRow (lexicalFittedPrograms s V TV M (argumentMeasure F) B T) s body Γ
      (numberedTerm h ty k l r) p vertices ctx result →
    HeadProvider F G s body →
    Nonempty (Derivation body Γ (unary (argumentReject G) z l)) →
    Nonempty (Derivation body Γ (unary (argumentReject G) z r)) →
    Nonempty (Derivation body Γ (memberGraph vertices (numberedTerm h ty k l r)))

def ExactOpenCoverTypeOnlyNumberedListScratch : Prop :=
  ∀ (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (h ty k l r p vertices ctx result : OTerm α),
    ParentRow (lexicalFittedPrograms s V TV M (argumentMeasure (typeLeafSharedMeasure M0)) B T)
      s body Γ (numberedTerm h ty k l r) p vertices ctx result →
    Nonempty (Derivation body Γ (unary (argumentReject (typeOnlyHeadGuard s)) z l)) →
    Nonempty (Derivation body Γ (unary (argumentReject (typeOnlyHeadGuard s)) z r)) →
    Nonempty (Derivation body Γ (memberGraph vertices (numberedTerm h ty k l r)))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverGuardedNumberedListTargets
