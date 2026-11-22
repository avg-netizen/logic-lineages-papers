module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedRoundApplicationTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredAuxExchangeTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedRoundApplicationCombinedTargets
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

/-- The single remaining premise about an exchange: an accepted edge `w → k`
of `E` carries the selected measure `μ` under `N` from `w` to `k`. -/
def MeasurePreservingEdge (E : Program 4) (N : Program 1) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (fctx fty μ w k : OTerm α),
    Nonempty (Derivation body Γ ((acceptEdge E fctx fty w k ⊓ unary N μ w).imp (unary N μ k)))

/-- Least half of the edge step on the actual combined programs: an accepted
function-level edge `w → k` at `rawCons dom cod` of the same chosen exchange and
window, a common selected measure of `w` and `k`, the two held type guards and
the argument window move the application least from `w` to `k`. -/
def ExactCombinedApplicationLeastStep : Prop :=
  ∀ (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (base : Program 2) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ctx dom cod arg μ m w k : OTerm α),
    let P := combinedPrograms s V TV M M0 B T
    let W := thinMatchingWindow P.cover s P.W P.V
    let X := guardedExchange P.cover s (thinPairedExchange (directedX base P.V))
    Nonempty (Derivation body Γ (unary TV (suc z) dom ⊓ unary TV (suc z) cod)) →
    Nonempty (Derivation body Γ (unary (refitGuard s T) (suc z) dom ⊓ unary (refitGuard s T) (suc z) cod)) →
    Nonempty (Derivation body Γ (windowAt W ctx dom arg)) →
    Nonempty (Derivation body Γ (acceptEdge (edge4 X W) ctx (rawCons dom cod) w k)) →
    Nonempty (Derivation body Γ (unary (selectedMeasure P.R) μ w)) →
    Nonempty (Derivation body Γ (unary (selectedMeasure P.R) μ k)) →
    Nonempty (Derivation body Γ (leastGraph P.cover X W s ctx cod (auxiliaryTerm dom cod w arg) m)) →
    Nonempty (Derivation body Γ (leastGraph P.cover X W s ctx cod (auxiliaryTerm dom cod k arg) m))

/-- Discharge of the relative edge premise of the round induction on the actual
combined programs, under exactly the measure-preservation premise. -/
def ExactCombinedApplicationEdgeStepAt : Prop :=
  ∀ (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (base : Program 2) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ctx dom cod arg μ m : OTerm α),
    let P := combinedPrograms s V TV M M0 B T
    let W := thinMatchingWindow P.cover s P.W P.V
    let X := guardedExchange P.cover s (thinPairedExchange (directedX base P.V))
    MeasurePreservingEdge (edge4 X W) (selectedMeasure P.R) →
    Nonempty (Derivation body Γ (unary TV (suc z) dom ⊓ unary TV (suc z) cod)) →
    Nonempty (Derivation body Γ (unary (refitGuard s T) (suc z) dom ⊓ unary (refitGuard s T) (suc z) cod)) →
    Nonempty (Derivation body Γ (windowAt W ctx dom arg)) →
    ApplicationEdgeStepAt (edge4 X W) (selectedMeasure P.R) P.cover X W s body Γ
      ctx (rawCons dom cod) ctx cod dom cod arg μ m

/-- The application least is constant on every actual finite round of the
function's members computation (same chosen exchange and window at function
type `rawCons dom cod`, from seed `f`), under the measure-preservation premise:
every member `k` keeps the seed's selected measure `μ`, and the application of
`k` to `arg` has the seed application's successful least `m`. -/
def ExactCombinedRoundApplicationLeast : Prop :=
  ∀ (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (base : Program 2) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ctx dom cod f arg μ m i vertices out k : OTerm α),
    let P := combinedPrograms s V TV M M0 B T
    let W := thinMatchingWindow P.cover s P.W P.V
    let X := guardedExchange P.cover s (thinPairedExchange (directedX base P.V))
    MeasurePreservingEdge (edge4 X W) (selectedMeasure P.R) →
    Nonempty (Derivation body Γ (unary TV (suc z) dom ⊓ unary TV (suc z) cod)) →
    Nonempty (Derivation body Γ (unary (refitGuard s T) (suc z) dom ⊓ unary (refitGuard s T) (suc z) cod)) →
    Nonempty (Derivation body Γ (windowAt W ctx dom arg)) →
    Nonempty (Derivation body Γ (unary (selectedMeasure P.R) μ f)) →
    Nonempty (Derivation body Γ (leastGraph P.cover X W s ctx cod (auxiliaryTerm dom cod f arg) m)) →
    Nonempty (Derivation body Γ (roundGraph (edge4 X W) out i vertices ctx (rawCons dom cod) f)) →
    Nonempty (Derivation body Γ (memberGraph out k)) →
    Nonempty (Derivation body Γ (unary (selectedMeasure P.R) μ k ⊓
      leastGraph P.cover X W s ctx cod (auxiliaryTerm dom cod k arg) m))

/-- For the measured variant of the guarded paired exchange (over
`measuredExchange M D`), measure preservation is a theorem, for any cover,
settings, measure program, base exchange and window. -/
def ExactMeasuredExchangePreservesMeasure : Prop :=
  ∀ (C : Program 3) (s : Settings) (M : Program 1) (D : Program 2) (W : Program 3),
    MeasurePreservingEdge (edge4 (guardedExchange C s (thinPairedExchange (measuredExchange M D))) W) M

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedRoundApplicationCombinedTargets
