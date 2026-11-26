module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverMixedLeafArgumentTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRestrictedListWindowTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverRestrictedMixedListTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowFieldAlgorithm (unpack)
open NumberedWindowInternalSparsePathEnvelope (run)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnTargets (ordinaryKey)
open NumberedWindowInternalCoverNumberedLayerTargets (numberedTerm)
open NumberedWindowInternalCoverRefinedInductionDispatchTargets (ParentRow)
open NumberedWindowInternalCoverLambdaBoundCoherenceTargets (lexicalFittedPrograms)
open NumberedWindowInternalCoverArgumentMemoTargets (argumentMeasure)
open NumberedWindowInternalCoverArgumentGuardTargets (argumentReject)
open NumberedWindowInternalCoverNamedLeafMeasureTargets (namedSharedMeasure)
open NumberedWindowInternalCoverRestrictedListWindowTargets (restrictedListBase)
open NumberedWindowInternalCoverMixedLeafArgumentTargets (mixedLeafHead OriginalMixedLeaf)

def OriginalMixedArguments (s : Settings) (raw : Nat) : Prop :=
  ∃ xs, unpack raw = some xs ∧ ∀ h ∈ xs, OriginalMixedLeaf s h

def ExactCoverMixedArgumentDomain : Prop :=
  ∀ (s : Settings) (raw : Nat),
    run (argumentReject (mixedLeafHead s)) raw = 0 ↔ OriginalMixedArguments s raw

/-- A separate restricted typed-window selection, using the very same
measured mixed leaf guard at both ordinary and numbered positions. -/
abbrev restrictedMixedPrograms (s : Settings) (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) :=
  lexicalFittedPrograms s V TV M (argumentMeasure (namedSharedMeasure M0))
    (restrictedListBase (mixedLeafHead s) B) T

def ExactOpenCoverRestrictedOrdinaryMixedScratch : Prop :=
  ∀ (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (h a p vertices ctx result : OTerm α),
    ParentRow (restrictedMixedPrograms s V TV M M0 B T) s body Γ (ordinaryKey h a)
      p vertices ctx result →
    Nonempty (Derivation body Γ (memberGraph vertices (ordinaryKey h a)))

def ExactOpenCoverRestrictedNumberedMixedScratch : Prop :=
  ∀ (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (h ty k l r p vertices ctx result : OTerm α),
    ParentRow (restrictedMixedPrograms s V TV M M0 B T) s body Γ (numberedTerm h ty k l r)
      p vertices ctx result →
    Nonempty (Derivation body Γ (memberGraph vertices (numberedTerm h ty k l r)))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverRestrictedMixedListTargets
