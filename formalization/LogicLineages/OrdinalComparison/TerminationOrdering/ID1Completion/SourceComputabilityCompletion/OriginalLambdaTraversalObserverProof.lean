module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalObserverInductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalSelectionTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalObserverProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open OriginalLambdaTraversalSelection OriginalLambdaTraversalObserver OriginalLambdaTraversalObserverSyntaxProof
open OriginalLambdaTraversalObserverBindingProof
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Eliminate the actual right-payload query and discharge the strong IH.
The result observes the original C graph with no extra child or fixedness premise. -/
theorem observationsAtInput (data : Data) (window : Program 1)
    (out input typ parameter mark : OrdinaryArithmetic.Term alpha)
    (hp : Nonempty (Derivation body Delta (premises data window out input typ parameter))) :
    Nonempty (Derivation body Delta (observations out input mark)) := by
  apply programCases InternalUnpair.right (Fin.cons input Fin.elim0) _
  intro beta j Theta payload hj hr
  rw [observationsRename]
  simp only [consTermRename,emptyRename] at hr
  have hp' := renameInto hp j Theta hj
  rw [premisesRename] at hp'
  exact atPayloadApply data window payload (input.relabel j) (typ.relabel j)
    (out.relabel j) (parameter.relabel j) (mark.relabel j)
    (OriginalLambdaTraversalObserverInductionProof.payloadObservers data window payload) hr hp'

/-- All five frozen observer contracts, for arbitrary original tuples and
window programs. No native calibration or unresolved supplier is assumed. -/
theorem actualOriginalLambdaTraversalObserverLaws :
    OriginalLambdaTraversalSelectionTargets.ActualOriginalLambdaTraversalObserverLaws := by
  intro data window
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro body alpha Delta out input typ parameter mark
    obtain ⟨h⟩ := observationsAtInput (body := body)
      (Delta := premises data window out input typ parameter :: Delta)
      data window out input typ parameter mark ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionLeft h)⟩
  · intro body alpha Delta out input typ parameter mark
    obtain ⟨h⟩ := observationsAtInput (body := body)
      (Delta := premises data window out input typ parameter :: Delta)
      data window out input typ parameter mark ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionLeft (Derivation.conjunctionRight h))⟩
  · intro body alpha Delta out input typ parameter mark
    obtain ⟨h⟩ := observationsAtInput (body := body)
      (Delta := premises data window out input typ parameter :: Delta)
      data window out input typ parameter mark ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionLeft
      (Derivation.conjunctionRight (Derivation.conjunctionRight h)))⟩
  · intro body alpha Delta out input typ parameter mark
    obtain ⟨h⟩ := observationsAtInput (body := body)
      (Delta := premises data window out input typ parameter :: Delta)
      data window out input typ parameter mark ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionLeft
      (Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.conjunctionRight h))))⟩
  · intro body alpha Delta out input typ parameter mark
    obtain ⟨h⟩ := observationsAtInput (body := body)
      (Delta := premises data window out input typ parameter :: Delta)
      data window out input typ parameter mark ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionRight
      (Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.conjunctionRight h))))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalObserverProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalObserverProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalObserverProof.actualOriginalLambdaTraversalObserverLaws
