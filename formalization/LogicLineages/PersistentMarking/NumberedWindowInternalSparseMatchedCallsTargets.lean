module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFormationRepresentativeTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTransitivityTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseMatchedCallsTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open SourceComputabilityFormulaSupportProof (existsOne)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparsePathAdvanceTargets (actualCalls)
open NumberedWindowInternalSparsePositiveTransitivityTargets (supplied)
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalSparseStructuralApplicationTargets (window)
open NumberedWindowInternalSparseFormationRepresentativeTargets (formation RepresentativeAt)

def pulled {α : Type} (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings) (raw : Program 5)
    (ctx cod parent target : OTerm α) : Formula α :=
  let j : α → α ⊕ Fin 1 := Sum.inl
  let earlier : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  existsOne (leastGraph C X W s (ctx.relabel j) (cod.relabel j) (parent.relabel j) earlier ⊓
    supplied raw (packedLeastProgram C X W s) (ctx.relabel j) (cod.relabel j) earlier (target.relabel j))

/-- The actual checked hop can start and finish at representatives different
from its two raw terms. A later application result determines the destination
class. Both an earlier result and its positive reduction witness are produced. -/
def MatchedCallsAt (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings) (raw : Program 5) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ctx dom cod arg fn next q child r value : OTerm α),
    let least := packedLeastProgram C X W s
    let input := formation W ctx dom cod arg ⊓ (actualCalls raw least ctx (rawCons dom cod) fn next q child r ⊓
      leastGraph C X W s ctx cod (auxiliaryTerm dom cod next arg) value)
    Nonempty (Derivation body Γ (input.imp (pulled C X W s raw ctx cod (auxiliaryTerm dom cod fn arg) value)))

def ExactMatchedCalls : Prop := ∀ (C root other baseW : Program 3) (X : Program 2) (V : Program 1) (s : Settings),
  let W := window C s baseW V
  RepresentativeAt C s X W → MatchedCallsAt C X W s (typedRaw5 root other W V)

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseMatchedCallsTargets
