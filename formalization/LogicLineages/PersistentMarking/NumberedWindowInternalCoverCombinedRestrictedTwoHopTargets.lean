module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedSingletonTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTransitivityTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedTwoHopTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalFiniteBlocks (block)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparsePositiveTransitivityTargets (supplied)
open NumberedWindowInternalCoverCombinedRestrictedSingletonTargets (thinHopData thinProvided)
open NumberedWindowInternalCoverCombinedRestrictedRawHopTargets (thinRawAt)
open NumberedWindowInternalCoverCombinedRestrictedTargets (combinedPrograms)
open NumberedWindowInternalCoverCombinedRestrictedWrapperTargets (thinMatchingWindow)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm functionWitnessTerm)
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z rawCons)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSettingsGrammarGuardDefinitions (refitGuard)

/-- Keep the two actual outer least reports and hide the actual composed code
only within the original positive `supplied` binder. -/
def pathData {α : Type} (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (raw : Program 5) (ctx cod src dst left right : OTerm α) : Formula α :=
  (leastGraph C X W s ctx cod src left ⊓ leastGraph C X W s ctx cod dst right) ⊓
    supplied raw (packedLeastProgram C X W s) ctx cod left right

def pathRow {α : Type} (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (raw : Program 5) (ctx cod src dst : OTerm α) : Formula (α ⊕ Fin 2) :=
  let j : α → α ⊕ Fin 2 := Sum.inl
  pathData C X W s raw (ctx.relabel j) (cod.relabel j) (src.relabel j) (dst.relabel j)
    (.var (.inr 0)) (.var (.inr 1))

abbrev suppliedPath {α : Type} (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (raw : Program 5) (ctx cod src dst : OTerm α) : Formula α :=
  block (pathRow C X W s raw ctx cod src dst)

def ExactOpenCoverThinTwoHop : Prop :=
  ∀ (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings) (raw : Program 5)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ctx cod src first mid second dst : OTerm α),
    Nonempty (Derivation body Γ (thinProvided C X W s raw ctx cod src first mid)) →
    Nonempty (Derivation body Γ (thinProvided C X W s raw ctx cod mid second dst)) →
    Nonempty (Derivation body Γ (suppliedPath C X W s raw ctx cod src dst))

/-- Same original lexical context, fixed argument and wrapped callbacks on
both hops. No equality between the two outer least values is asserted. -/
def ExactOpenCoverCombinedRestrictedTwoHop : Prop :=
  ∀ (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (root other : Program 3) (X : Program 2)
    (s : Settings) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ctx dom cod fn first middle second next arg : OTerm α),
    let P := combinedPrograms s V TV M M0 B T
    let W := thinMatchingWindow P.cover s P.W P.V
    let raw := typedRaw5 root other W P.V
    Nonempty (Derivation body Γ (unary TV (suc z) dom ⊓ unary TV (suc z) cod)) →
    Nonempty (Derivation body Γ (unary (refitGuard s T) (suc z) dom ⊓ unary (refitGuard s T) (suc z) cod)) →
    Nonempty (Derivation body Γ (windowAt W ctx dom arg)) →
    Nonempty (Derivation body Γ (thinRawAt raw ctx (rawCons dom cod) fn first middle)) →
    Nonempty (Derivation body Γ (thinRawAt raw ctx (rawCons dom cod) middle second next)) →
    Nonempty (Derivation body Γ (suppliedPath P.cover X W s raw ctx cod
      (auxiliaryTerm dom cod fn arg) (auxiliaryTerm dom cod next arg)))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedTwoHopTargets
