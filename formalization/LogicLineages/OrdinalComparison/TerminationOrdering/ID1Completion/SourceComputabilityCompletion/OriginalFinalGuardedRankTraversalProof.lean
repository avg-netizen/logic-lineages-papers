module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalGuardedRankInductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalSelectionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRankGuardedLeafProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalGuardedRankTraversalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open OriginalLambdaTraversalSelection OriginalFinalGuardedRankObserverProof OriginalFinalGuardedRankSyntaxProof
open OriginalFinalGuardedRankBindingProof
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Eliminate the actual right-payload query and discharge the strong IH.
The result observes the original C graph with no extra child or fixedness premise. -/
theorem observationsAtInput (data : Data) (window : Program 1) (supply : OriginalFinalGuardedRankLeafProof.OtherLaw data window)
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
    (OriginalFinalGuardedRankInductionProof.payloadObservers data window supply payload) hr hp'

/-- Exact all-input internal rank traversal at the once-refined tuple. -/
theorem actualOriginalFinalGuardedTraversalRank :
    OriginalFinalGuardedRankTargets.ActualOriginalFinalGuardedTraversalRank := by
  intro p H G W
  let r := OriginalFinalGuardedRank.refined p H G W
  have supply : OriginalFinalGuardedRankLeafProof.OtherLaw r.base r.window := by
    intro body alpha Delta out input typ parameter mark hw hs ht hl
    exact OriginalRankGuardedLeafProof.otherRank p H G W out input parameter mark
      hw (InternalApplicationStepPeelSupportProof.andLeft hs) ht hl
  intro body alpha Delta out input typ parameter mark
  obtain ⟨h⟩ := observationsAtInput (body := body)
    (Delta := premises r.base r.window out input typ parameter :: Delta)
    r.base r.window supply out input typ parameter mark ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalGuardedRankTraversalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalGuardedRankTraversalProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalGuardedRankTraversalProof.actualOriginalFinalGuardedTraversalRank
