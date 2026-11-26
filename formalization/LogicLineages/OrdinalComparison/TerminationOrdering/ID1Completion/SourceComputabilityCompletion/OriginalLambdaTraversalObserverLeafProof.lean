module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLeafObserverProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalObserverDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalLeafProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalObserverLeafProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalLambdaTraversalSelection OriginalLambdaTraversalObserver
open OriginalLambdaTraversalLeafObserverProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- The actual OTHER-tag machine equation reduces to the SAME selected leaf.
All five pre-existing leaf preservation theorems apply to its actual output. -/
theorem atOtherTag (data : Data) (window : Program 1) (out input typ parameter mark : OTerm alpha)
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
  have hw := andLeft hp
  have hv := andLeft (andLeft (andRight hp))
  exact andIntro (rootMark data window out input parameter mark hw hv hl)
    (andIntro (variableMark data window out input parameter mark hw hv hl)
      (andIntro (neutralityMark data window out input parameter mark hw hv hl)
        (andIntro (spineMark data window out input parameter mark hw hv hl)
          (bottomMark data window out input parameter mark hw hv hl))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalObserverLeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalObserverLeafProof
