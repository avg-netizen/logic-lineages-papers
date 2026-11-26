module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedPairedAuxTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverOccurrenceTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedCrossCoverTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary rawCons)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparseCoverScratch (coverOption scratchVertices)
open NumberedWindowInternalSparseCoverOccurrenceTargets (occursInCover)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSettingsGrammarGuardDefinitions (refitGuard)
open NumberedWindowInternalCoverCombinedRestrictedTargets (combinedPrograms)
open NumberedWindowInternalCoverCombinedRestrictedWrapperTargets (thinMatchingWindow)
open NumberedWindowInternalCoverCombinedRestrictedDirectedXTargets (directedX)
open NumberedWindowInternalCoverCombinedRestrictedPairedAuxTargets (thinPairedExchange)
open NumberedWindowInternalSparseCoverGuardedExchangeTargets (guardedExchange)
open NumberedWindowInternalSparseScalarEdge (edgeGraph)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)

/-- All reports use the *same actual ordered list code*, never extensional
sets or the later exchanged/reachable pool. Both own-key reports are derived. -/
structure CrossCoverReports (C : Program 3) (s : Settings) (body : Positive (Fin 1)) {α : Type}
    (Γ : List (Formula α)) (a b vertices : OTerm α) : Prop where
  optionA : Nonempty (Derivation body Γ (unary (coverOption C s) (suc vertices) a))
  optionB : Nonempty (Derivation body Γ (unary (coverOption C s) (suc vertices) b))
  scratchA : Nonempty (Derivation body Γ (unary (scratchVertices C s) vertices a))
  scratchB : Nonempty (Derivation body Γ (unary (scratchVertices C s) vertices b))
  memberA : Nonempty (Derivation body Γ (memberGraph vertices a))
  memberB : Nonempty (Derivation body Γ (memberGraph vertices b))
  crossAB : Nonempty (Derivation body Γ (occursInCover C s a b))
  crossBA : Nonempty (Derivation body Γ (occursInCover C s b a))

def ExactOpenCoverThinCrossCover : Prop :=
  ∀ (C baseW : Program 3) (V : Program 1) (s : Settings) (body : Positive (Fin 1))
    (α : Type) (Γ : List (Formula α)) (ctx ty a b vertices : OTerm α),
    let W := thinMatchingWindow C s baseW V
    Nonempty (Derivation body Γ (windowAt W ctx ty a)) →
    Nonempty (Derivation body Γ (windowAt W ctx ty b)) →
    Nonempty (Derivation body Γ (unary (coverOption C s) (suc vertices) a)) →
    Nonempty (Derivation body Γ (unary (coverOption C s) (suc vertices) b)) →
    CrossCoverReports C s body Γ a b vertices

/-- Actual conditional paired parent edge with both literal seed occurrences
in its common physical cover, but no claim of reached-pool closure. -/
def ExactOpenCoverCombinedRestrictedPairedCrossCover : Prop :=
  ∀ (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (base : Program 2) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ctx dom cod f g arg m : OTerm α) (goal : Formula α),
    let P := combinedPrograms s V TV M M0 B T
    let W := thinMatchingWindow P.cover s P.W P.V
    let D := directedX base P.V
    let X := guardedExchange P.cover s (thinPairedExchange D)
    let a := auxiliaryTerm dom cod f arg
    let b := auxiliaryTerm dom cod g arg
    Nonempty (Derivation body Γ (unary TV (suc z) dom ⊓ unary TV (suc z) cod)) →
    Nonempty (Derivation body Γ (unary (refitGuard s T) (suc z) dom ⊓ unary (refitGuard s T) (suc z) cod)) →
    Nonempty (Derivation body Γ (windowAt W ctx dom arg)) →
    Nonempty (Derivation body Γ (edgeGraph D W ctx (rawCons dom cod) f g)) →
    Nonempty (Derivation body Γ (edgeGraph D W ctx (rawCons dom cod) g f)) →
    Nonempty (Derivation body Γ (unary (selectedMeasure P.R) m a)) →
    Nonempty (Derivation body Γ (unary (selectedMeasure P.R) m b)) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (vertices : OTerm β),
      (∀ p ∈ Γ, p.relabel j ∈ Δ) →
      CrossCoverReports P.cover s body Δ (a.relabel j) (b.relabel j) vertices →
      Nonempty (Derivation body Δ (edgeGraph X W (ctx.relabel j) (cod.relabel j) (a.relabel j) (b.relabel j))) →
      Nonempty (Derivation body Δ (goal.relabel j))) →
    Nonempty (Derivation body Γ goal)

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedCrossCoverTargets
