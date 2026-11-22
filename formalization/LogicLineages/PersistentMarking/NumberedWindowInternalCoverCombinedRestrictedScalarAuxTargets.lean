module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedWrappedAuxTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScalarEdgeTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedScalarAuxTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
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
open NumberedWindowInternalSparseScalarEdge (edgeGraph exchangeTape)

/-- The unpaid condition is a local raw exchange callback, not an
assumption of typed edge closure, reachability, or least congruence. -/
def localAuxExchange {α : Type} (X : Program 2) (V : Program 1)
    (dom cod f g arg : OTerm α) : Formula α :=
  let a := auxiliaryTerm dom cod f arg
  let b := auxiliaryTerm dom cod g arg
  (programGraph X (suc z) (exchangeTape f g) ⊓
    (unary V (suc z) a ⊓ unary V (suc z) b)).imp
      (programGraph X (suc z) (exchangeTape a b))

def ExactOpenCoverCombinedRestrictedScalarAux : Prop :=
  ∀ (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (X : Program 2) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx dom cod f g arg : OTerm α),
    let P := combinedPrograms s V TV M M0 B T
    let W := thinMatchingWindow P.cover s P.W P.V
    Nonempty (Derivation body Γ (unary TV (suc z) dom ⊓ unary TV (suc z) cod)) →
    Nonempty (Derivation body Γ (unary (refitGuard s T) (suc z) dom ⊓ unary (refitGuard s T) (suc z) cod)) →
    Nonempty (Derivation body Γ (windowAt W ctx dom arg)) →
    Nonempty (Derivation body Γ (edgeGraph X W ctx (rawCons dom cod) f g)) →
    Nonempty (Derivation body Γ (localAuxExchange X P.V dom cod f g arg)) →
    Nonempty (Derivation body Γ (edgeGraph X W ctx cod (auxiliaryTerm dom cod f arg) (auxiliaryTerm dom cod g arg)))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedScalarAuxTargets
