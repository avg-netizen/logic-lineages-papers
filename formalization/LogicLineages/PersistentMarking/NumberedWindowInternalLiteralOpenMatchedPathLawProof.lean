module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralOpenMatchedAdvanceLawProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveWindowTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralOpenMatchedPathLawProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalLiteralOpenMatchedReportProof
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparsePositiveHeadDecompositionTargets (finishAt positiveAt)
open NumberedWindowInternalLiteralOpenMatchedReportProof (pulled)
open NumberedWindowInternalLiteralOpenMatchedAdvanceLawProof (MatchedAdvanceAt resultOrPath)

def ExactMatchedFinish : Prop := ∀ (K : MatchContext) (L : Program 3) (raw : Program 5),
  MatchedAdvanceAt K L raw → ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ctx dom cod arg fn next cert value : OTerm α),
    let done := finishAt raw (L) ctx (rawCons dom cod) fn cert next
    let later := reported L ctx cod (auxiliaryTerm dom cod next arg) value
    Nonempty (Derivation body Γ ((typedFormation K ctx dom cod arg ⊓ (done ⊓ later)).imp
      (resultOrPath K L raw ctx cod (auxiliaryTerm dom cod fn arg) value)))

def MatchedPathAt (K : MatchContext) (L : Program 3) (raw : Program 5) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ctx dom cod arg fn next cert value : OTerm α),
    let positive := positiveAt raw (L) ctx (rawCons dom cod) fn cert next
    let later := reported L ctx cod (auxiliaryTerm dom cod next arg) value
    Nonempty (Derivation body Γ ((typedFormation K ctx dom cod arg ⊓ (positive ⊓ later)).imp
      (pulled L raw ctx cod (auxiliaryTerm dom cod fn arg) value)))

def ExactMatchedPath : Prop := ∀ (K : MatchContext) (L : Program 3) (raw : Program 5),
  MatchedAdvanceAt K L raw → MatchedPathAt K L raw

#print axioms ExactMatchedFinish
#print axioms MatchedPathAt
#print axioms ExactMatchedPath
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralOpenMatchedPathLawProof
