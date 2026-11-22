module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredDispatchTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedEmptyTargets
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
open NumberedWindowInternalCoverNumberedMeasureCombineTargets (NumberedJoinBounds)
open NumberedWindowInternalCoverNumberedMeasureSelectedTargets (numberedSharedMeasure numberedMeasuredPrograms)

abbrev emptyNumberedKey {α : Type} (h ty k : OTerm α) := numberedTerm h ty k z z

def ExactOpenCoverNumberedEmptyMeasure : Prop :=
  ∀ (M A : Program 1) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (h ty k p : OTerm α),
    Nonempty (Derivation body Γ (unary (numberedSharedMeasure M A) p (emptyNumberedKey h ty k))) →
    NumberedJoinBounds body Γ p k z z z z k

def ExactOpenCoverNumberedEmptyFittedScratch : Prop :=
  ∀ (V TV M A : Program 1) (B : Program 2) (T : Program 1) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (h ty k p vertices ctx result : OTerm α),
    ParentRow (numberedMeasuredPrograms s V TV M A B T) s body Γ (emptyNumberedKey h ty k)
      p vertices ctx result →
    Nonempty (Derivation body Γ (memberGraph vertices (emptyNumberedKey h ty k)))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedEmptyTargets
