module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedRoundApplicationRepresentativeTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedMeasuredRoundTargets
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
open NumberedWindowInternalSparseScalarEdge (edge4)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparseOpenRoundsTargets (roundGraph)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalMeasuredAuxExchangeTargets (measuredExchange)
open NumberedWindowInternalCoverCombinedRestrictedRoundApplicationTargets

/-- Edge premise discharged with no remaining premise when BOTH the
function-level round and the application-level least use the one measured
exchange `Xm` (same cover and window). Layout of
`ExactMeasuredCombinedApplicationEdgeStepAt`, with the application exchange
`X` replaced by `Xm`. -/
def ExactFullyMeasuredApplicationEdgeStepAt : Prop :=
  ∀ (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (base : Program 2) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ctx dom cod arg μ m : OTerm α),
    let P := combinedPrograms s V TV M M0 B T
    let W := thinMatchingWindow P.cover s P.W P.V
    let D := directedX base P.V
    let Xm := guardedExchange P.cover s (thinPairedExchange (measuredExchange (selectedMeasure P.R) D))
    Nonempty (Derivation body Γ (unary TV (suc z) dom ⊓ unary TV (suc z) cod)) →
    Nonempty (Derivation body Γ (unary (refitGuard s T) (suc z) dom ⊓ unary (refitGuard s T) (suc z) cod)) →
    Nonempty (Derivation body Γ (windowAt W ctx dom arg)) →
    ApplicationEdgeStepAt (edge4 Xm W) (selectedMeasure P.R) P.cover Xm W s body Γ
      ctx (rawCons dom cod) ctx cod dom cod arg μ m

/-- Round theorem with one exchange system throughout: the round is computed
with `edge4 Xm W` and the application least is the least of `Xm`. No measure
premise. Layout of `ExactMeasuredCombinedRoundApplicationLeast`. -/
def ExactFullyMeasuredRoundApplicationLeast : Prop :=
  ∀ (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (base : Program 2) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ctx dom cod f arg μ m i vertices out k : OTerm α),
    let P := combinedPrograms s V TV M M0 B T
    let W := thinMatchingWindow P.cover s P.W P.V
    let D := directedX base P.V
    let Xm := guardedExchange P.cover s (thinPairedExchange (measuredExchange (selectedMeasure P.R) D))
    Nonempty (Derivation body Γ (unary TV (suc z) dom ⊓ unary TV (suc z) cod)) →
    Nonempty (Derivation body Γ (unary (refitGuard s T) (suc z) dom ⊓ unary (refitGuard s T) (suc z) cod)) →
    Nonempty (Derivation body Γ (windowAt W ctx dom arg)) →
    Nonempty (Derivation body Γ (unary (selectedMeasure P.R) μ f)) →
    Nonempty (Derivation body Γ (leastGraph P.cover Xm W s ctx cod (auxiliaryTerm dom cod f arg) m)) →
    Nonempty (Derivation body Γ (roundGraph (edge4 Xm W) out i vertices ctx (rawCons dom cod) f)) →
    Nonempty (Derivation body Γ (memberGraph out k)) →
    Nonempty (Derivation body Γ (unary (selectedMeasure P.R) μ k ⊓
      leastGraph P.cover Xm W s ctx cod (auxiliaryTerm dom cod k arg) m))

/-- Application to a fixed argument factors through the function's least
representative, with the function's least and both application leasts taken
for the one measured exchange `Xm`. The seed's measure is not an input; the
seed application's least `m` is. Layout of
`ExactMeasuredCombinedLeastRepresentativeApplication`. -/
def ExactFullyMeasuredLeastRepresentativeApplication : Prop :=
  ∀ (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (base : Program 2) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ctx dom cod f x arg m : OTerm α),
    let P := combinedPrograms s V TV M M0 B T
    let W := thinMatchingWindow P.cover s P.W P.V
    let D := directedX base P.V
    let Xm := guardedExchange P.cover s (thinPairedExchange (measuredExchange (selectedMeasure P.R) D))
    Nonempty (Derivation body Γ (unary TV (suc z) dom ⊓ unary TV (suc z) cod)) →
    Nonempty (Derivation body Γ (unary (refitGuard s T) (suc z) dom ⊓ unary (refitGuard s T) (suc z) cod)) →
    Nonempty (Derivation body Γ (windowAt W ctx dom arg)) →
    Nonempty (Derivation body Γ (leastGraph P.cover Xm W s ctx cod (auxiliaryTerm dom cod f arg) m)) →
    Nonempty (Derivation body Γ (leastGraph P.cover Xm W s ctx (rawCons dom cod) f x)) →
    Nonempty (Derivation body Γ (leastGraph P.cover Xm W s ctx cod (auxiliaryTerm dom cod x arg) m))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedMeasuredRoundTargets
