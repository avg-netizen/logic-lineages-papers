module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedPairedSharedMeasureTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredAuxExchangeTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedMeasuredPairedTargets
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
open NumberedWindowInternalSparseScalarEdge (edgeGraph)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalMeasuredAuxExchangeTargets (measuredExchange)

/-- The single-exchange step entirely over the MEASURED guarded paired exchange
`Xm`: one accepted function-level edge of `Xm` between `f` and `g` at
`rawCons dom cod`, the two held type guards and the argument window give the
accepted application-level edge of the same `Xm` between the two auxiliary
applications. No measure report, cover report, reverse edge, pool or length is
an input: the reverse direction and the common function measure are recovered
from the one measured paired edge. -/
def ExactOpenCoverCombinedRestrictedMeasuredPairedEdge : Prop :=
  ∀ (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (base : Program 2) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ctx dom cod f g arg : OTerm α),
    let P := combinedPrograms s V TV M M0 B T
    let W := thinMatchingWindow P.cover s P.W P.V
    let Xm := guardedExchange P.cover s
      (thinPairedExchange (measuredExchange (selectedMeasure P.R) (directedX base P.V)))
    let a := auxiliaryTerm dom cod f arg
    let b := auxiliaryTerm dom cod g arg
    Nonempty (Derivation body Γ (unary TV (suc z) dom ⊓ unary TV (suc z) cod)) →
    Nonempty (Derivation body Γ (unary (refitGuard s T) (suc z) dom ⊓ unary (refitGuard s T) (suc z) cod)) →
    Nonempty (Derivation body Γ (windowAt W ctx dom arg)) →
    Nonempty (Derivation body Γ (edgeGraph Xm W ctx (rawCons dom cod) f g)) →
    Nonempty (Derivation body Γ (edgeGraph Xm W ctx cod a b))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedMeasuredPairedTargets
