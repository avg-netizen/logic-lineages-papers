module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedPairedCommonLeastTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedRecursionTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedPairedSharedMeasureTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z eqn)
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
open NumberedWindowInternalSparseScalarEdge (edgeGraph)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalCoverSharedRecursionTargets (sharedMeasure)

/-- Analogue of #858's equality for the shared selected measure (the one the
combined programs use): a common selected measure of the two functions and
the literally identical argument give equal selected measures of the two
auxiliary applications. Existence of the application measures is held here. -/
def ExactOpenSharedAuxMeasureEquality : Prop :=
  ∀ (M : Program 1) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (dom cod fn fn' arg m x y : OTerm α),
    Nonempty (Derivation body Γ (unary (sharedMeasure M) m fn)) →
    Nonempty (Derivation body Γ (unary (sharedMeasure M) m fn')) →
    Nonempty (Derivation body Γ (unary (sharedMeasure M) x (auxiliaryTerm dom cod fn arg))) →
    Nonempty (Derivation body Γ (unary (sharedMeasure M) y (auxiliaryTerm dom cod fn' arg))) →
    Nonempty (Derivation body Γ (eqn x y))

/-- At the actual chosen programs: a common selected measure of the two
functions gives one common selected measure of the two applications (a fresh
`p`, handed to the continuation). No application measure is an input. -/
def ExactOpenCoverCombinedRestrictedPairedSharedMeasureParent : Prop :=
  ∀ (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (dom cod f g arg m : OTerm α) (goal : Formula α),
    let P := combinedPrograms s V TV M M0 B T
    let a := auxiliaryTerm dom cod f arg
    let b := auxiliaryTerm dom cod g arg
    Nonempty (Derivation body Γ (unary (selectedMeasure P.R) m f)) →
    Nonempty (Derivation body Γ (unary (selectedMeasure P.R) m g)) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (p : OTerm β),
      (∀ q ∈ Γ, q.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (unary (selectedMeasure P.R) p (a.relabel j))) →
      Nonempty (Derivation body Δ (unary (selectedMeasure P.R) p (b.relabel j))) →
      Nonempty (Derivation body Δ (goal.relabel j))) →
    Nonempty (Derivation body Γ goal)

/-- #1386's paired guarded edge with the shared *application* measure replaced
by a shared *function* measure `m` of `f` and `g` (same selected program). -/
def ExactOpenCoverCombinedRestrictedPairedSharedMeasureEdge : Prop :=
  ∀ (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (base : Program 2) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ctx dom cod f g arg m : OTerm α),
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
    Nonempty (Derivation body Γ (unary (selectedMeasure P.R) m f)) →
    Nonempty (Derivation body Γ (unary (selectedMeasure P.R) m g)) →
    Nonempty (Derivation body Γ (edgeGraph X W ctx cod a b))

/-- The common successful least of task 1 with the shared application measure
replaced by a shared function measure. No least call, application measure,
cover report, pool or length is an input. -/
def ExactOpenCoverCombinedRestrictedPairedSharedMeasureCommonLeast : Prop :=
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
    Nonempty (Derivation body Γ (unary (selectedMeasure P.R) m f)) →
    Nonempty (Derivation body Γ (unary (selectedMeasure P.R) m g)) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (x : OTerm β),
      (∀ p ∈ Γ, p.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ
        (leastGraph P.cover X W s (ctx.relabel j) (cod.relabel j) (a.relabel j) x)) →
      Nonempty (Derivation body Δ
        (leastGraph P.cover X W s (ctx.relabel j) (cod.relabel j) (b.relabel j) x)) →
      Nonempty (Derivation body Δ (goal.relabel j))) →
    Nonempty (Derivation body Γ goal)

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedPairedSharedMeasureTargets
