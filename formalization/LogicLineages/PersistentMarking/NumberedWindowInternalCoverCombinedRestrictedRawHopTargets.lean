module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedWrappedAuxTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawLiftTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedRawHopTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary rawCons)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm functionWitnessTerm)
open NumberedWindowInternalSettingsGrammarGuardDefinitions (refitGuard)
open NumberedWindowInternalCoverCombinedRestrictedTargets (combinedPrograms)
open NumberedWindowInternalCoverCombinedRestrictedWrapperTargets (thinMatchingWindow)

/-- The literal original positive raw graph, with exactly five ordered
coordinates; no alternate raw certificate encoding. -/
abbrev thinRawAt {α : Type} (raw : Program 5) (ctx ty src witness dst : OTerm α) : Formula α :=
  programGraph raw (suc z) ![ctx,ty,src,witness,dst]

/-- One actual forward function-side raw hop at the exact same selected
combined typed raw checker. The function endpoints are not external
window assumptions; actual acceptance of the child raw hop supplies both. -/
def ExactOpenCoverCombinedRestrictedRawHop : Prop :=
  ∀ (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (root other : Program 3)
    (s : Settings) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ctx dom cod fn child next arg : OTerm α),
    let P := combinedPrograms s V TV M M0 B T
    let W := thinMatchingWindow P.cover s P.W P.V
    let raw := typedRaw5 root other W P.V
    Nonempty (Derivation body Γ (unary TV (suc z) dom ⊓ unary TV (suc z) cod)) →
    Nonempty (Derivation body Γ (unary (refitGuard s T) (suc z) dom ⊓ unary (refitGuard s T) (suc z) cod)) →
    Nonempty (Derivation body Γ (windowAt W ctx dom arg)) →
    Nonempty (Derivation body Γ (thinRawAt raw ctx (rawCons dom cod) fn child next)) →
    Nonempty (Derivation body Γ
      (thinRawAt raw ctx cod (auxiliaryTerm dom cod fn arg) (functionWitnessTerm child)
        (auxiliaryTerm dom cod next arg)))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedRawHopTargets
