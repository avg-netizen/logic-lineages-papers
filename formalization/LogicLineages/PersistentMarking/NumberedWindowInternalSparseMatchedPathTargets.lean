module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseMatchedAdvanceTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveWindowTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseMatchedPathTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparsePositiveHeadDecompositionTargets (finishAt positiveAt)
open NumberedWindowInternalSparseFormationRepresentativeTargets (formation)
open NumberedWindowInternalSparseMatchedCallsTargets (pulled)
open NumberedWindowInternalSparseMatchedAdvanceTargets (MatchedAdvanceAt resultOrPath)

def ExactMatchedFinish : Prop := ∀ (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings) (raw : Program 5),
  MatchedAdvanceAt C X W s raw → ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ctx dom cod arg fn next cert value : OTerm α),
    let done := finishAt raw (packedLeastProgram C X W s) ctx (rawCons dom cod) fn cert next
    let later := leastGraph C X W s ctx cod (auxiliaryTerm dom cod next arg) value
    Nonempty (Derivation body Γ ((formation W ctx dom cod arg ⊓ (done ⊓ later)).imp
      (resultOrPath C X W s raw ctx cod (auxiliaryTerm dom cod fn arg) value)))

def MatchedPathAt (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings) (raw : Program 5) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ctx dom cod arg fn next cert value : OTerm α),
    let positive := positiveAt raw (packedLeastProgram C X W s) ctx (rawCons dom cod) fn cert next
    let later := leastGraph C X W s ctx cod (auxiliaryTerm dom cod next arg) value
    Nonempty (Derivation body Γ ((formation W ctx dom cod arg ⊓ (positive ⊓ later)).imp
      (pulled C X W s raw ctx cod (auxiliaryTerm dom cod fn arg) value)))

def ExactMatchedPath : Prop := ∀ (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings) (raw : Program 5),
  MatchedAdvanceAt C X W s raw → MatchedPathAt C X W s raw

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseMatchedPathTargets
