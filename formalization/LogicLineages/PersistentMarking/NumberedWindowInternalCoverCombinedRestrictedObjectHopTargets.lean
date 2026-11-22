module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedSingletonTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedObjectHopTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z rawCons unary)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparsePathAdvanceTargets (selectedGraph)
open NumberedWindowInternalSparsePathSuccessfulAdvanceTargets (hopCalls)
open NumberedWindowInternalCoverCombinedRestrictedSingletonTargets (thinProvided)
open NumberedWindowInternalCoverCombinedRestrictedTargets (combinedPrograms)
open NumberedWindowInternalCoverCombinedRestrictedWrapperTargets (thinMatchingWindow)
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm functionWitnessTerm)
open NumberedWindowInternalSettingsGrammarGuardDefinitions (refitGuard)

/-- Exact CPS for one held original successful selected object cell.
The original raw source/witness/target come from that cell; neither
its class coordinates nor a fresh unrelated choice is substituted. -/
def ExactOpenCoverCombinedRestrictedObjectHop : Prop :=
  ∀ (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (root other : Program 3) (X : Program 2)
    (s : Settings) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ctx dom cod arg current hop target : OTerm α) (goal : Formula α),
    let P := combinedPrograms s V TV M M0 B T
    let W := thinMatchingWindow P.cover s P.W P.V
    let raw := typedRaw5 root other W P.V
    let least := packedLeastProgram P.cover X W s
    Nonempty (Derivation body Γ (unary TV (suc z) dom ⊓ unary TV (suc z) cod)) →
    Nonempty (Derivation body Γ (unary (refitGuard s T) (suc z) dom ⊓ unary (refitGuard s T) (suc z) cod)) →
    Nonempty (Derivation body Γ (windowAt W ctx dom arg)) →
    Nonempty (Derivation body Γ (selectedGraph raw least (suc target) ctx (rawCons dom cod) (suc current) hop)) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (q w r : OTerm β),
      (∀ a ∈ Γ, a.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (hopCalls raw least (ctx.relabel j) (rawCons (dom.relabel j) (cod.relabel j))
        (current.relabel j) (hop.relabel j) (target.relabel j) q w r)) →
      Nonempty (Derivation body Δ (thinProvided P.cover X W s raw (ctx.relabel j) (cod.relabel j)
        (auxiliaryTerm (dom.relabel j) (cod.relabel j) q (arg.relabel j)) (functionWitnessTerm w)
        (auxiliaryTerm (dom.relabel j) (cod.relabel j) r (arg.relabel j)))) →
      Nonempty (Derivation body Δ (goal.relabel j))) →
    Nonempty (Derivation body Γ goal)

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedObjectHopTargets
