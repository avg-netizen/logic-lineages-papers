module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRestrictedMixedListTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRestrictedLambdaFragmentOwnTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnTargets (ordinaryKey)
open NumberedWindowInternalCoverNumberedLayerTargets (numberedTerm)
open NumberedWindowInternalCoverLambdaLayerTargets (lambdaTerm)
open NumberedWindowInternalCoverRefinedInductionDispatchTargets (ParentRow)
open NumberedWindowInternalCoverNamedLeafMeasureTargets (namedSharedMeasure)
open NumberedWindowInternalCoverArgumentMemoTargets (argumentMeasure)
open NumberedWindowInternalCoverMixedLeafArgumentTargets (mixedLeafHead)
open NumberedWindowInternalCoverRestrictedListWindowTargets (restrictedListBase)
open NumberedWindowInternalCoverRestrictedLambdaFragmentTargets (lambdaFragmentBase)
open NumberedWindowInternalCoverAuxFragmentGuardTargets (fragmentGuard)
open NumberedWindowInternalCoverLambdaLexicalWindowTargets (lambdaLexicalWindow)
open NumberedWindowInternalCoverLambdaBoundCoherenceTargets (lexicalFittedPrograms)
open NumberedWindowInternalAuxWindowOpenTargets (windowGraph)

/-- One actual restricted callback on the original contextual tape.
The mixed arguments apply at literal tags four and five; the literal
tag-two filter is inside their unchanged fallback. -/
abbrev combinedCallback (s : Settings) (B : Program 2) : Program 2 :=
  restrictedListBase (mixedLeafHead s) (lambdaFragmentBase B)

abbrev combinedPrograms (s : Settings) (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) :=
  lexicalFittedPrograms s V TV M (argumentMeasure (namedSharedMeasure M0)) (combinedCallback s B) T

def ExactOpenCoverCombinedRestrictedLambdaBase : Prop :=
  ∀ (s : Settings) (B : Program 2) (body : Positive (Fin 1)) (α : Type)
    (Γ : List (Formula α)) (ctx dom q out : OTerm α),
    Nonempty (Derivation body Γ
      (programGraph (combinedCallback s B) (suc out) ![ctx,lambdaTerm dom q])) →
    Nonempty (Derivation body Γ
      (programGraph (lambdaFragmentBase B) (suc out) ![ctx,lambdaTerm dom q]))

def ExactOpenCoverCombinedRestrictedLambdaGuard : Prop :=
  ∀ (s : Settings) (B : Program 2) (T : Program 1) (body : Positive (Fin 1)) (α : Type)
    (Γ : List (Formula α)) (ctx dom q result : OTerm α),
    Nonempty (Derivation body Γ
      (windowGraph (lambdaLexicalWindow s (combinedCallback s B) T) ctx result (lambdaTerm dom q))) →
    Nonempty (Derivation body Γ (unary fragmentGuard (suc z) q))

def ExactOpenCoverCombinedRestrictedOrdinaryOwn : Prop :=
  ∀ (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (h a p vertices ctx result : OTerm α),
    ParentRow (combinedPrograms s V TV M M0 B T) s body Γ (ordinaryKey h a) p vertices ctx result →
    Nonempty (Derivation body Γ (memberGraph vertices (ordinaryKey h a)))

def ExactOpenCoverCombinedRestrictedNumberedOwn : Prop :=
  ∀ (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (h ty k l r p vertices ctx result : OTerm α),
    ParentRow (combinedPrograms s V TV M M0 B T) s body Γ (numberedTerm h ty k l r) p vertices ctx result →
    Nonempty (Derivation body Γ (memberGraph vertices (numberedTerm h ty k l r)))

/-- The same row includes its genuine earlier same-W bounded own-key
formula. Only the separate external fragment-guard premise is removed. -/
def ExactOpenCoverCombinedRestrictedLambdaOwn : Prop :=
  ∀ (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (dom q p vertices ctx result : OTerm α),
    ParentRow (combinedPrograms s V TV M M0 B T) s body Γ (lambdaTerm dom q) p vertices ctx result →
    Nonempty (Derivation body Γ (memberGraph vertices (lambdaTerm dom q)))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedTargets
