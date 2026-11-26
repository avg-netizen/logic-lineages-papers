module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralOpenMatchedReportProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralOpenMatchedAdvanceLawProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalLiteralOpenMatchedReportProof
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons suc)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparsePathAdvanceTargets (selectedGraph)
open NumberedWindowInternalLiteralOpenMatchedReportProof (pulled MatchedCallsAt)

/-- At an empty remaining certificate the result itself suffices. A positive
remaining certificate carries its earlier result and genuine positive witness. -/
def resultOrPath {α : Type} (K : MatchContext) (L : Program 3) (raw : Program 5)
    (ctx cod parent value : OTerm α) : Formula α :=
  reported L ctx cod parent value ⊔ pulled L raw ctx cod parent value

def MatchedAdvanceAt (K : MatchContext) (L : Program 3) (raw : Program 5) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ctx dom cod arg fn next hop value : OTerm α),
    let least := L
    let step := selectedGraph raw least (suc next) ctx (rawCons dom cod) (suc fn) hop
    let later := resultOrPath K L raw ctx cod (auxiliaryTerm dom cod next arg) value
    Nonempty (Derivation body Γ ((typedFormation K ctx dom cod arg ⊓ (step ⊓ later)).imp
      (pulled L raw ctx cod (auxiliaryTerm dom cod fn arg) value)))

def ExactMatchedAdvance : Prop := ∀ (K : MatchContext) (L : Program 3) (raw : Program 5),
  MatchedCallsAt K L raw → MatchedAdvanceAt K L raw

#print axioms resultOrPath
#print axioms MatchedAdvanceAt
#print axioms ExactMatchedAdvance
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralOpenMatchedAdvanceLawProof
