module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedRawHopTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressSingletonTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedDomainTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedSingletonTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalFiniteBlocks (block)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary rawCons)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm functionWitnessTerm)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparsePackedDomainTargets (hasLeast)
open NumberedWindowInternalSparsePositiveHeadDecompositionTargets (positiveAt)
open NumberedWindowInternalSparseAddressSingletonTargets (singletonCertificate)
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalSettingsGrammarGuardDefinitions (refitGuard)
open NumberedWindowInternalCoverCombinedRestrictedTargets (combinedPrograms)
open NumberedWindowInternalCoverCombinedRestrictedWrapperTargets (thinMatchingWindow)
open NumberedWindowInternalCoverCombinedRestrictedRawHopTargets (thinRawAt)

/-- Thin recut of the original hopData, row and provided expressions.
This declares no nominal historical constant equality. -/
def thinHopData {α : Type} (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (raw : Program 5) (ctx cod src wr dst left right : OTerm α) : Formula α :=
  (leastGraph C X W s ctx cod src left ⊓ leastGraph C X W s ctx cod dst right) ⊓
    positiveAt raw (packedLeastProgram C X W s) ctx cod left (singletonCertificate right src wr dst) right

def thinHopRow {α : Type} (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (raw : Program 5) (ctx cod src wr dst : OTerm α) : Formula (α ⊕ Fin 2) :=
  let j : α → α ⊕ Fin 2 := Sum.inl
  thinHopData C X W s raw (ctx.relabel j) (cod.relabel j) (src.relabel j) (wr.relabel j)
    (dst.relabel j) (.var (.inr 0)) (.var (.inr 1))

abbrev thinProvided {α : Type} (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (raw : Program 5) (ctx cod src wr dst : OTerm α) : Formula α :=
  block (thinHopRow C X W s raw ctx cod src wr dst)

def ExactOpenCoverThinSingletonFromAvailableLeast : Prop :=
  ∀ (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings) (raw : Program 5)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx ty src wr dst : OTerm α),
    Nonempty (Derivation body Γ (thinRawAt raw ctx ty src wr dst)) →
    Nonempty (Derivation body Γ (hasLeast C X W s ctx ty src)) →
    Nonempty (Derivation body Γ (hasLeast C X W s ctx ty dst)) →
    Nonempty (Derivation body Γ (thinProvided C X W s raw ctx ty src wr dst))

/-- One actual positive wrapped application certificate at two held
original parent tapes. The existential results need not agree. -/
def ExactOpenCoverCombinedRestrictedSingleton : Prop :=
  ∀ (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (root other : Program 3) (X : Program 2)
    (s : Settings) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ctx dom cod fn child next arg : OTerm α),
    let P := combinedPrograms s V TV M M0 B T
    let W := thinMatchingWindow P.cover s P.W P.V
    let raw := typedRaw5 root other W P.V
    Nonempty (Derivation body Γ (unary TV (suc z) dom ⊓ unary TV (suc z) cod)) →
    Nonempty (Derivation body Γ (unary (refitGuard s T) (suc z) dom ⊓ unary (refitGuard s T) (suc z) cod)) →
    Nonempty (Derivation body Γ (windowAt W ctx dom arg)) →
    Nonempty (Derivation body Γ (thinRawAt raw ctx (rawCons dom cod) fn child next)) →
    Nonempty (Derivation body Γ (thinProvided P.cover X W s raw ctx cod (auxiliaryTerm dom cod fn arg)
      (functionWitnessTerm child) (auxiliaryTerm dom cod next arg)))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedSingletonTargets
