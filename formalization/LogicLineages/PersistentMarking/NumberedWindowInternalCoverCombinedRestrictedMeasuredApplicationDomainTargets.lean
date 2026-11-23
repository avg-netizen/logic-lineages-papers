module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedMeasuredClassApplicationTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedDomainTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedMeasuredApplicationDomainTargets
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

/-- The exact literal measured exchange of the existing #1421/#1422,
at the specified cover, selected measure, and original directed D. -/
abbrev domainMeasuredExchange (C : Program 3) (s : Settings) (N : Program 1) (D : Program 2) : Program 2 :=
  guardedExchange C s (thinPairedExchange (measuredExchange N D))

/-- Existence is independent of the chosen exchange: the admitted
application has its own actual raw key in the original cover. -/
def ExactOpenCoverApplicationHasLeastFromWindow : Prop :=
  ∀ (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (X : Program 2) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx dom cod f arg : OTerm α),
    let P := combinedPrograms s V TV M M0 B T
    let W := thinMatchingWindow P.cover s P.W P.V
    Nonempty (Derivation body Γ (unary TV (suc z) dom ⊓ unary TV (suc z) cod)) →
    Nonempty (Derivation body Γ (unary (refitGuard s T) (suc z) dom ⊓ unary (refitGuard s T) (suc z) cod)) →
    Nonempty (Derivation body Γ (windowAt W ctx dom arg)) →
    Nonempty (Derivation body Γ (windowAt W ctx (rawCons dom cod) f)) →
    Nonempty (Derivation body Γ (hasLeast P.cover X W s ctx cod (auxiliaryTerm dom cod f arg)))

/-- The genuine simultaneous least reports supplied by the continuation.
The witness is chosen by the actual least program, not a Lean witness. -/
def CommonAppLeastK {α : Type} (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (body : Positive (Fin 1)) (Γ : List (Formula α)) (ctx cod a b : OTerm α) (goal : Formula α) : Prop :=
  ∀ (β : Type) (ρ : α → β) (Δ : List (Formula β)) (m : OTerm β),
    (∀ p ∈ Γ, p.relabel ρ ∈ Δ) →
    Nonempty (Derivation body Δ (leastGraph C X W s (ctx.relabel ρ) (cod.relabel ρ) (a.relabel ρ) m)) →
    Nonempty (Derivation body Δ (leastGraph C X W s (ctx.relabel ρ) (cod.relabel ρ) (b.relabel ρ) m)) →
    Nonempty (Derivation body Δ (goal.relabel ρ))

/-- #1421 with the seed application least obtained from its held actual
function window. The representative window is not an extra premise. -/
def ExactFullyMeasuredRepresentativeApplicationDomain : Prop :=
  ∀ (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (base : Program 2) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ctx dom cod f x arg : OTerm α) (goal : Formula α),
    let P := combinedPrograms s V TV M M0 B T
    let W := thinMatchingWindow P.cover s P.W P.V
    let Xm := domainMeasuredExchange P.cover s (selectedMeasure P.R) (directedX base P.V)
    Nonempty (Derivation body Γ (unary TV (suc z) dom ⊓ unary TV (suc z) cod)) →
    Nonempty (Derivation body Γ (unary (refitGuard s T) (suc z) dom ⊓ unary (refitGuard s T) (suc z) cod)) →
    Nonempty (Derivation body Γ (windowAt W ctx dom arg)) →
    Nonempty (Derivation body Γ (windowAt W ctx (rawCons dom cod) f)) →
    Nonempty (Derivation body Γ (leastGraph P.cover Xm W s ctx (rawCons dom cod) f x)) →
    CommonAppLeastK P.cover Xm W s body Γ ctx cod
      (auxiliaryTerm dom cod f arg) (auxiliaryTerm dom cod x arg) goal →
    Nonempty (Derivation body Γ goal)

/-- #1422 with both application least calls derived; both actual
function windows are kept explicit, separate from successful function least. -/
def ExactFullyMeasuredClassApplicationDomain : Prop :=
  ∀ (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (base : Program 2) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ctx dom cod f g x arg : OTerm α) (goal : Formula α),
    let P := combinedPrograms s V TV M M0 B T
    let W := thinMatchingWindow P.cover s P.W P.V
    let Xm := domainMeasuredExchange P.cover s (selectedMeasure P.R) (directedX base P.V)
    Nonempty (Derivation body Γ (unary TV (suc z) dom ⊓ unary TV (suc z) cod)) →
    Nonempty (Derivation body Γ (unary (refitGuard s T) (suc z) dom ⊓ unary (refitGuard s T) (suc z) cod)) →
    Nonempty (Derivation body Γ (windowAt W ctx dom arg)) →
    Nonempty (Derivation body Γ (windowAt W ctx (rawCons dom cod) f)) →
    Nonempty (Derivation body Γ (windowAt W ctx (rawCons dom cod) g)) →
    Nonempty (Derivation body Γ (leastGraph P.cover Xm W s ctx (rawCons dom cod) f x)) →
    Nonempty (Derivation body Γ (leastGraph P.cover Xm W s ctx (rawCons dom cod) g x)) →
    CommonAppLeastK P.cover Xm W s body Γ ctx cod
      (auxiliaryTerm dom cod f arg) (auxiliaryTerm dom cod g arg) goal →
    Nonempty (Derivation body Γ goal)

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedMeasuredApplicationDomainTargets
