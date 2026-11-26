module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseMatchedCallsTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseMatchedAdvanceTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons suc)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparsePathAdvanceTargets (selectedGraph)
open NumberedWindowInternalSparseFormationRepresentativeTargets (formation)
open NumberedWindowInternalSparseMatchedCallsTargets (pulled MatchedCallsAt)

/-- At an empty remaining certificate the result itself suffices. A positive
remaining certificate carries its earlier result and genuine positive witness. -/
def resultOrPath {α : Type} (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings) (raw : Program 5)
    (ctx cod parent value : OTerm α) : Formula α :=
  leastGraph C X W s ctx cod parent value ⊔ pulled C X W s raw ctx cod parent value

def MatchedAdvanceAt (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings) (raw : Program 5) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ctx dom cod arg fn next hop value : OTerm α),
    let least := packedLeastProgram C X W s
    let step := selectedGraph raw least (suc next) ctx (rawCons dom cod) (suc fn) hop
    let later := resultOrPath C X W s raw ctx cod (auxiliaryTerm dom cod next arg) value
    Nonempty (Derivation body Γ ((formation W ctx dom cod arg ⊓ (step ⊓ later)).imp
      (pulled C X W s raw ctx cod (auxiliaryTerm dom cod fn arg) value)))

def ExactMatchedAdvance : Prop := ∀ (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings) (raw : Program 5),
  MatchedCallsAt C X W s raw → MatchedAdvanceAt C X W s raw

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseMatchedAdvanceTargets
