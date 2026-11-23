module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedSeedGrammarTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedWrapperTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedDomainTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureCombineOpenTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxLeastAtKnownScopesTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open SourceComputabilityFormulaSupportProof (existsOne)
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
open NumberedWindowInternalChosenAuxMeasureCombineOpenTargets (boundBody codePair)

structure ActualAuxCoverDomainInputs (V N : Program 1) (X : Program 2) (W : Program 3) (s : Settings)
    (body : Positive (Fin 1)) {α : Type} (Γ : List (Formula α))
    (ctx dom cod fn arg fx ax p mf ma df bf da ba : OTerm α) : Prop where
  contextAtParent : Nonempty (Derivation body Γ (windowAt thinContextPresent ctx cod (auxiliaryTerm dom cod fn arg)))
  functionLeast : Nonempty (Derivation body Γ (leastGraph (selectedCover V N) X W s ctx (rawCons dom cod) fn fx))
  argumentLeast : Nonempty (Derivation body Γ (leastGraph (selectedCover V N) X W s ctx dom arg ax))
  functionValid : Nonempty (Derivation body Γ (unary V (suc z) fn))
  argumentValid : Nonempty (Derivation body Γ (unary V (suc z) arg))
  functionMeasure : Nonempty (Derivation body Γ (unary N mf fn))
  argumentMeasure : Nonempty (Derivation body Γ (unary N ma arg))
  functionPair : Nonempty (Derivation body Γ (codePair mf df bf))
  argumentPair : Nonempty (Derivation body Γ (codePair ma da ba))
  parentValid : Nonempty (Derivation body Γ (unary V (suc z) (auxiliaryTerm dom cod fn arg)))
  parentMeasure : Nonempty (Derivation body Γ (unary N p (auxiliaryTerm dom cod fn arg)))
  parentBounds : Nonempty (Derivation body Γ (existsOne (boundBody p df da bf ba)))
  domainMember : Nonempty (Derivation body Γ (memberGraph (typesTerm s α) dom))
  codomainMember : Nonempty (Derivation body Γ (memberGraph (typesTerm s α) cod))

def ExactOpenCoverAuxLeastAtKnownScopes : Prop :=
  ∀ (V N : Program 1) (X : Program 2) (W : Program 3) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ctx dom cod fn arg fx ax p mf ma df bf da ba : OTerm α),
    ActualAuxCoverDomainInputs V N X W s body Γ ctx dom cod fn arg fx ax p mf ma df bf da ba →
    Nonempty (Derivation body Γ (hasLeast (selectedCover V N) X W s ctx cod (auxiliaryTerm dom cod fn arg)))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxLeastAtKnownScopesTargets
