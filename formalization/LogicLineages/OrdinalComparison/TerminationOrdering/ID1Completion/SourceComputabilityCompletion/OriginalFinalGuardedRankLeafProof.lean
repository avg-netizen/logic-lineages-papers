module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLeafObserverProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalGuardedRankObserverProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalLeafProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalGuardedRankLeafProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalLambdaTraversalSelection OriginalFinalGuardedRankObserverProof
open OriginalLambdaTraversalLeafObserverProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- A derivation supplier for precisely the OTHER leaf, not a Program field. -/
def OtherLaw (data : Data) (window : Program 1) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (out input typ parameter mark : OTerm alpha),
    Nonempty (Derivation body Delta (OriginalFunctionNeutrality.windowGraph window input parameter)) →
    Nonempty (Derivation body Delta
      (InternalParameterizedCanonicalResultFold.sourcePremises (leafData data window) input typ parameter)) →
    Nonempty (Derivation body Delta
      (graph1 OriginalLambdaTraversalInternal.otherTag InternalOriginalStepGuard.one input)) →
    Nonempty (Derivation body Delta (graph2 (leaf data window) out input parameter)) →
    Nonempty (Derivation body Delta (observations out input mark))

/-- The actual OTHER-tag machine equation reduces to the SAME selected leaf.
The rank supplier applies to that actual output. -/
theorem atOtherTag (data : Data) (window : Program 1) (supply : OtherLaw data window) (out input typ parameter mark : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (premises data window out input typ parameter)))
    (ht : Nonempty (Derivation body Delta
      (graph1 OriginalLambdaTraversalInternal.otherTag InternalOriginalStepGuard.one input))) :
    Nonempty (Derivation body Delta (observations out input mark)) := by
  obtain ⟨law⟩ := OriginalLambdaTraversalInternalLeafProof.actualOriginalLambdaTraversalInternalLeaf
    body (leaf data window) alpha Delta input out parameter
  obtain ⟨htProof⟩ := ht
  obtain ⟨hc⟩ := andRight (andRight hp)
  have hl : Nonempty (Derivation body Delta (graph2 (leaf data window) out input parameter)) :=
    ⟨Derivation.implicationElimination (Derivation.conjunctionLeft
      (Derivation.implicationElimination law htProof)) hc⟩
  exact supply body alpha Delta out input typ parameter mark
    (andLeft hp) (andLeft (andRight hp)) ⟨htProof⟩ hl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalGuardedRankLeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalGuardedRankLeafProof
