module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedCrossCoverTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedPairedMinimumTargets
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

/-- The paired guarded auxiliary edge of the same chosen programs as a plain
derivation in the original context, from the parent function exchange in one
direction, its reverse, both type guards, the argument window and the shared
selected measure. No cover report, pool or length is an input or an output. -/
def ExactOpenCoverCombinedRestrictedPairedEdge : Prop :=
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
    Nonempty (Derivation body Γ (unary (selectedMeasure P.R) m a)) →
    Nonempty (Derivation body Γ (unary (selectedMeasure P.R) m b)) →
    Nonempty (Derivation body Γ (edgeGraph X W ctx cod a b))

/-- Opposite actual paired guarded edges between the two applications force
the two successful packed least outputs of the same chosen cover, exchange and
window programs to be equal. The two least calls are held, not derived. -/
def ExactOpenCoverCombinedRestrictedPairedEdgeMinimum : Prop :=
  ∀ (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (base : Program 2) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ctx dom cod f g arg x y : OTerm α),
    let P := combinedPrograms s V TV M M0 B T
    let W := thinMatchingWindow P.cover s P.W P.V
    let X := guardedExchange P.cover s (thinPairedExchange (directedX base P.V))
    let a := auxiliaryTerm dom cod f arg
    let b := auxiliaryTerm dom cod g arg
    Nonempty (Derivation body Γ (edgeGraph X W ctx cod a b)) →
    Nonempty (Derivation body Γ (edgeGraph X W ctx cod b a)) →
    Nonempty (Derivation body Γ (leastGraph P.cover X W s ctx cod a x)) →
    Nonempty (Derivation body Γ (leastGraph P.cover X W s ctx cod b y)) →
    Nonempty (Derivation body Γ (eqn x y))

/-- The same conclusion from the parent function exchange itself: the two
opposite parent edges, guards, argument window and shared measure, with the
two successful least calls at the applications held. -/
def ExactOpenCoverCombinedRestrictedPairedParentMinimum : Prop :=
  ∀ (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (base : Program 2) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ctx dom cod f g arg m x y : OTerm α),
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
    Nonempty (Derivation body Γ (leastGraph P.cover X W s ctx cod a x)) →
    Nonempty (Derivation body Γ (leastGraph P.cover X W s ctx cod b y)) →
    Nonempty (Derivation body Γ (eqn x y))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedPairedMinimumTargets
