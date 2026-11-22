module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeOnlyArgumentListTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverGuardedOrdinaryListTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalCoverOrdinaryMeasureTargets (selectedArgsMeasure)
open NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnTargets (ordinaryKey)
open NumberedWindowInternalCoverRefinedInductionDispatchTargets (ParentRow)
open NumberedWindowInternalCoverLambdaBoundCoherenceTargets (lexicalFittedPrograms)
open NumberedWindowInternalCoverArgumentMemoTargets (argumentMeasure)
open NumberedWindowInternalCoverArgumentGuardTargets (argumentReject)
open NumberedWindowInternalCoverArgumentGrammarInductionTargets (HeadProvider argumentExists)
open NumberedWindowInternalCoverTypeOnlyArgumentListTargets (typeOnlyHeadGuard)
open NumberedWindowInternalCoverTypeLeafMeasureTargets (typeLeafSharedMeasure)

/-- The existing ordinary empty clamping program preserves the real
output of this particular physical memo, including its true zero row. -/
def ExactOpenCoverArgumentMemoClamp : Prop :=
  ∀ (F : Program 1) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (raw p : OTerm α),
    Nonempty (Derivation body Γ (unary (argumentMeasure F) p raw)) →
    Nonempty (Derivation body Γ (unary (selectedArgsMeasure (argumentMeasure F)) p raw))

def ExactOpenCoverMeasuredOrdinaryListScratch : Prop :=
  ∀ (V TV M F : Program 1) (B : Program 2) (T : Program 1) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (h a p vertices ctx result : OTerm α),
    ParentRow (lexicalFittedPrograms s V TV M (argumentMeasure F) B T) s body Γ
      (ordinaryKey h a) p vertices ctx result →
    Nonempty (Derivation body Γ (argumentExists F s a)) →
    Nonempty (Derivation body Γ (memberGraph vertices (ordinaryKey h a)))

def ExactOpenCoverGuardedOrdinaryListScratch : Prop :=
  ∀ (V TV M F G : Program 1) (B : Program 2) (T : Program 1) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (h a p vertices ctx result : OTerm α),
    ParentRow (lexicalFittedPrograms s V TV M (argumentMeasure F) B T) s body Γ
      (ordinaryKey h a) p vertices ctx result →
    HeadProvider F G s body →
    Nonempty (Derivation body Γ (unary (argumentReject G) z a)) →
    Nonempty (Derivation body Γ (memberGraph vertices (ordinaryKey h a)))

def ExactOpenCoverTypeOnlyOrdinaryListScratch : Prop :=
  ∀ (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (h a p vertices ctx result : OTerm α),
    ParentRow (lexicalFittedPrograms s V TV M (argumentMeasure (typeLeafSharedMeasure M0)) B T)
      s body Γ (ordinaryKey h a) p vertices ctx result →
    Nonempty (Derivation body Γ (unary (argumentReject (typeOnlyHeadGuard s)) z a)) →
    Nonempty (Derivation body Γ (memberGraph vertices (ordinaryKey h a)))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverGuardedOrdinaryListTargets
