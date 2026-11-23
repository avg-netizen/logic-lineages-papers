module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedMeasuredApplicationDomainTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedDomainTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedMeasuredLeastDomainTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary rawCons)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSettingsGrammarGuardDefinitions (refitGuard)
open NumberedWindowInternalCoverCombinedRestrictedTargets (combinedPrograms)
open NumberedWindowInternalCoverCombinedRestrictedWrapperTargets (thinMatchingWindow)
open NumberedWindowInternalCoverCombinedRestrictedDirectedXTargets (directedX)
open NumberedWindowInternalCoverCombinedRestrictedPairedAuxTargets (thinPairedExchange)
open NumberedWindowInternalSparseCoverGuardedExchangeTargets (guardedExchange)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparsePackedDomainTargets (hasLeast)
open NumberedWindowInternalMeasuredAuxExchangeTargets (measuredExchange)

open NumberedWindowInternalCoverCombinedRestrictedMeasuredApplicationDomainTargets (domainMeasuredExchange CommonAppLeastK)

/-- #1421 with the seed application least obtained from its actual
function least, not from any additional function/representative window. -/
def ExactFullyMeasuredRepresentativeApplicationLeastDomain : Prop :=
  ∀ (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (base : Program 2) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ctx dom cod f x arg : OTerm α) (goal : Formula α),
    let P := combinedPrograms s V TV M M0 B T
    let W := thinMatchingWindow P.cover s P.W P.V
    let Xm := domainMeasuredExchange P.cover s (selectedMeasure P.R) (directedX base P.V)
    Nonempty (Derivation body Γ (unary TV (suc z) dom ⊓ unary TV (suc z) cod)) →
    Nonempty (Derivation body Γ (unary (refitGuard s T) (suc z) dom ⊓ unary (refitGuard s T) (suc z) cod)) →
    Nonempty (Derivation body Γ (windowAt W ctx dom arg)) →
    Nonempty (Derivation body Γ (leastGraph P.cover Xm W s ctx (rawCons dom cod) f x)) →
    CommonAppLeastK P.cover Xm W s body Γ ctx cod
      (auxiliaryTerm dom cod f arg) (auxiliaryTerm dom cod x arg) goal →
    Nonempty (Derivation body Γ goal)

/-- #1422 with both application least calls derived from the two held
function leasts, without additional function windows. -/
def ExactFullyMeasuredClassApplicationLeastDomain : Prop :=
  ∀ (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (base : Program 2) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ctx dom cod f g x arg : OTerm α) (goal : Formula α),
    let P := combinedPrograms s V TV M M0 B T
    let W := thinMatchingWindow P.cover s P.W P.V
    let Xm := domainMeasuredExchange P.cover s (selectedMeasure P.R) (directedX base P.V)
    Nonempty (Derivation body Γ (unary TV (suc z) dom ⊓ unary TV (suc z) cod)) →
    Nonempty (Derivation body Γ (unary (refitGuard s T) (suc z) dom ⊓ unary (refitGuard s T) (suc z) cod)) →
    Nonempty (Derivation body Γ (windowAt W ctx dom arg)) →
    Nonempty (Derivation body Γ (leastGraph P.cover Xm W s ctx (rawCons dom cod) f x)) →
    Nonempty (Derivation body Γ (leastGraph P.cover Xm W s ctx (rawCons dom cod) g x)) →
    CommonAppLeastK P.cover Xm W s body Γ ctx cod
      (auxiliaryTerm dom cod f arg) (auxiliaryTerm dom cod g arg) goal →
    Nonempty (Derivation body Γ goal)

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedMeasuredLeastDomainTargets
