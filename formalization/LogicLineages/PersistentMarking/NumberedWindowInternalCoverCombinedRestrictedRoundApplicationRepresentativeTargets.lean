module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedRoundApplicationCombinedTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedRoundApplicationRepresentativeTargets
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
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)
open NumberedWindowInternalMeasuredAuxExchangeTargets (measuredExchange)
open NumberedWindowInternalCoverCombinedRestrictedRoundApplicationTargets
open NumberedWindowInternalCoverCombinedRestrictedRoundApplicationCombinedTargets

/-- Generic: the function's own successful packed least `x` (function-level
programs `Cf Xf Wf sf`, the least whose members are computed with
`edge4 Xf Wf`) satisfies the application motive of the seed `f`, under the
relative one-edge premise for that same edge program. -/
def ExactLeastRepresentativeApplication : Prop :=
  ∀ (Cf : Program 3) (Xf : Program 2) (Wf : Program 3) (sf : Settings)
    (N : Program 1) (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (fctx fty f x ctx ty dom cod arg μ m : OTerm α),
    ApplicationEdgeStepAt (edge4 Xf Wf) N C X W s body Γ fctx fty ctx ty dom cod arg μ m →
    Nonempty (Derivation body Γ (appMotive N C X W s ctx ty dom cod arg μ m f)) →
    Nonempty (Derivation body Γ (leastGraph Cf Xf Wf sf fctx fty f x)) →
    Nonempty (Derivation body Γ (appMotive N C X W s ctx ty dom cod arg μ m x))

/-- An accepted edge of the guarded paired exchange over `measuredExchange M D`
is an accepted edge of the guarded paired exchange over `D` (same cover,
settings and window). -/
def ExactMeasuredToPlainEdge : Prop :=
  ∀ (C : Program 3) (s : Settings) (M : Program 1) (D : Program 2) (W : Program 3)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx ty w k : OTerm α),
    Nonempty (Derivation body Γ
      (acceptEdge (edge4 (guardedExchange C s (thinPairedExchange (measuredExchange M D))) W) ctx ty w k)) →
    Nonempty (Derivation body Γ (acceptEdge (edge4 (guardedExchange C s (thinPairedExchange D)) W) ctx ty w k))

/-- Edge premise discharged with no remaining premise when the function-level
round uses the measured exchange `Xm` and the application least uses the
chosen unmeasured exchange `X` (same cover and window). -/
def ExactMeasuredCombinedApplicationEdgeStepAt : Prop :=
  ∀ (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (base : Program 2) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ctx dom cod arg μ m : OTerm α),
    let P := combinedPrograms s V TV M M0 B T
    let W := thinMatchingWindow P.cover s P.W P.V
    let D := directedX base P.V
    let X := guardedExchange P.cover s (thinPairedExchange D)
    let Xm := guardedExchange P.cover s (thinPairedExchange (measuredExchange (selectedMeasure P.R) D))
    Nonempty (Derivation body Γ (unary TV (suc z) dom ⊓ unary TV (suc z) cod)) →
    Nonempty (Derivation body Γ (unary (refitGuard s T) (suc z) dom ⊓ unary (refitGuard s T) (suc z) cod)) →
    Nonempty (Derivation body Γ (windowAt W ctx dom arg)) →
    ApplicationEdgeStepAt (edge4 Xm W) (selectedMeasure P.R) P.cover X W s body Γ
      ctx (rawCons dom cod) ctx cod dom cod arg μ m

/-- Round theorem for the measured function-level exchange, no measure premise. -/
def ExactMeasuredCombinedRoundApplicationLeast : Prop :=
  ∀ (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (base : Program 2) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ctx dom cod f arg μ m i vertices out k : OTerm α),
    let P := combinedPrograms s V TV M M0 B T
    let W := thinMatchingWindow P.cover s P.W P.V
    let D := directedX base P.V
    let X := guardedExchange P.cover s (thinPairedExchange D)
    let Xm := guardedExchange P.cover s (thinPairedExchange (measuredExchange (selectedMeasure P.R) D))
    Nonempty (Derivation body Γ (unary TV (suc z) dom ⊓ unary TV (suc z) cod)) →
    Nonempty (Derivation body Γ (unary (refitGuard s T) (suc z) dom ⊓ unary (refitGuard s T) (suc z) cod)) →
    Nonempty (Derivation body Γ (windowAt W ctx dom arg)) →
    Nonempty (Derivation body Γ (unary (selectedMeasure P.R) μ f)) →
    Nonempty (Derivation body Γ (leastGraph P.cover X W s ctx cod (auxiliaryTerm dom cod f arg) m)) →
    Nonempty (Derivation body Γ (roundGraph (edge4 Xm W) out i vertices ctx (rawCons dom cod) f)) →
    Nonempty (Derivation body Γ (memberGraph out k)) →
    Nonempty (Derivation body Γ (unary (selectedMeasure P.R) μ k ⊓
      leastGraph P.cover X W s ctx cod (auxiliaryTerm dom cod k arg) m))

/-- Application to a fixed argument factors through the function's least
representative (unmeasured chosen exchange), under the measure-preservation
premise. The seed's measure is not an input; the seed application's least `m`
is. -/
def ExactCombinedLeastRepresentativeApplication : Prop :=
  ∀ (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (base : Program 2) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ctx dom cod f x arg m : OTerm α),
    let P := combinedPrograms s V TV M M0 B T
    let W := thinMatchingWindow P.cover s P.W P.V
    let X := guardedExchange P.cover s (thinPairedExchange (directedX base P.V))
    MeasurePreservingEdge (edge4 X W) (selectedMeasure P.R) →
    Nonempty (Derivation body Γ (unary TV (suc z) dom ⊓ unary TV (suc z) cod)) →
    Nonempty (Derivation body Γ (unary (refitGuard s T) (suc z) dom ⊓ unary (refitGuard s T) (suc z) cod)) →
    Nonempty (Derivation body Γ (windowAt W ctx dom arg)) →
    Nonempty (Derivation body Γ (leastGraph P.cover X W s ctx cod (auxiliaryTerm dom cod f arg) m)) →
    Nonempty (Derivation body Γ (leastGraph P.cover X W s ctx (rawCons dom cod) f x)) →
    Nonempty (Derivation body Γ (leastGraph P.cover X W s ctx cod (auxiliaryTerm dom cod x arg) m))

/-- The same with the function's least taken for the measured exchange `Xm`;
no measure premise remains. -/
def ExactMeasuredCombinedLeastRepresentativeApplication : Prop :=
  ∀ (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (base : Program 2) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ctx dom cod f x arg m : OTerm α),
    let P := combinedPrograms s V TV M M0 B T
    let W := thinMatchingWindow P.cover s P.W P.V
    let D := directedX base P.V
    let X := guardedExchange P.cover s (thinPairedExchange D)
    let Xm := guardedExchange P.cover s (thinPairedExchange (measuredExchange (selectedMeasure P.R) D))
    Nonempty (Derivation body Γ (unary TV (suc z) dom ⊓ unary TV (suc z) cod)) →
    Nonempty (Derivation body Γ (unary (refitGuard s T) (suc z) dom ⊓ unary (refitGuard s T) (suc z) cod)) →
    Nonempty (Derivation body Γ (windowAt W ctx dom arg)) →
    Nonempty (Derivation body Γ (leastGraph P.cover X W s ctx cod (auxiliaryTerm dom cod f arg) m)) →
    Nonempty (Derivation body Γ (leastGraph P.cover Xm W s ctx (rawCons dom cod) f x)) →
    Nonempty (Derivation body Γ (leastGraph P.cover X W s ctx cod (auxiliaryTerm dom cod x arg) m))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedRoundApplicationRepresentativeTargets
