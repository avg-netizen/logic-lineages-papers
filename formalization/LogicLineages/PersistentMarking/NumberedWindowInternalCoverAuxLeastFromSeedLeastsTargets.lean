module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxLeastAtKnownScopesTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedMeasureChildrenTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxLeastFromSeedLeastsTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary rawCons)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparsePackedDomainTargets (hasLeast)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalCoverSelectedGrammarAuxScratchTargets (selectedCover)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (typesTerm)
open NumberedWindowInternalCoverCombinedRestrictedWrapperTargets (thinContextPresent)
open NumberedWindowInternalCoverSharedRecursionTargets (sharedMeasure)

structure ActualAuxSeedInputs (V M : Program 1) (X : Program 2) (W : Program 3) (s : Settings)
    (body : Positive (Fin 1)) {α : Type} (Γ : List (Formula α))
    (ctx dom cod fn arg fx ax : OTerm α) : Prop where
  parsed : Nonempty (Derivation body Γ (windowAt thinContextPresent ctx cod (auxiliaryTerm dom cod fn arg)))
  functionLeast : Nonempty (Derivation body Γ (leastGraph (selectedCover V (sharedMeasure M)) X W s ctx
    (rawCons dom cod) fn fx))
  argumentLeast : Nonempty (Derivation body Γ (leastGraph (selectedCover V (sharedMeasure M)) X W s ctx dom arg ax))
  functionValid : Nonempty (Derivation body Γ (unary V (suc z) fn))
  argumentValid : Nonempty (Derivation body Γ (unary V (suc z) arg))
  parentValid : Nonempty (Derivation body Γ (unary V (suc z) (auxiliaryTerm dom cod fn arg)))
  domainMember : Nonempty (Derivation body Γ (memberGraph (typesTerm s α) dom))
  codomainMember : Nonempty (Derivation body Γ (memberGraph (typesTerm s α) cod))

/-- The two actual child leasts and the source syntax/type/parser evidence
supply a domain proof without any external measure reports. -/
def ExactOpenCoverAuxLeastFromSeedLeasts : Prop :=
  ∀ (V M : Program 1) (X : Program 2) (W : Program 3) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ctx dom cod fn arg fx ax : OTerm α),
    ActualAuxSeedInputs V M X W s body Γ ctx dom cod fn arg fx ax →
    Nonempty (Derivation body Γ (hasLeast (selectedCover V (sharedMeasure M)) X W s ctx cod
      (auxiliaryTerm dom cod fn arg)))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxLeastFromSeedLeastsTargets
