module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionGuardedIndexedTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionMinimumIndexedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalGuardedObserverWrapperProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverWrapperProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceBranchProof
open InternalApplicationCertifiedResultFoldClosureBridgeBranchProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalApplicationValidityStackAppendInductionCoreProof (formulaCases withHyp)
open InternalTagArithmeticSyntaxProof (eqn z suc sucRelabel zRelabel)
open OriginalTypedDecoderTransportLogicalProof (iffRename)
open OriginalIndexedObserverRangeSyntaxProof (rangeRename)
open OriginalIndexedObserverIteration
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Proof-only predicate at one fixed condition, preserving actual index and
runtime parameter. No change to a Program tuple. -/
def Keeps (condition R : Program 2) (observer : Program 3) : Prop :=
  Preservation ⟨R,condition,observer⟩

theorem projectionPreservation (condition : Program 2) (observer : Program 3) :
    Keeps condition (.projection 0) observer := by
  intro body alpha Delta out input parameter mark cutoff _ _ hr
  have he := valueUnique (.projection (0 : Fin 2)) out input ![input,parameter] hr
    (projectionValue 0 ![input,parameter])
  obtain ⟨hi⟩ := OriginalClassContextAllPositionSelectionOutputProof.observationOfEqual
    observer mark cutoff input out parameter he
  exact ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionRight hi) (Derivation.conjunctionLeft hi)⟩

theorem branchPreservation (condition C R S : Program 2) (observer : Program 3)
    (hR : Keeps condition R observer) (hS : Keeps condition S observer) :
    Keeps condition (InternalAcceptance.branch C R S) observer := by
  intro body alpha Delta out input parameter mark cutoff hRange ha hr
  change Nonempty (Derivation body Delta
    ((graph3 observer mark cutoff out parameter).iff (graph3 observer mark cutoff input parameter)))
  change Nonempty (Derivation body Delta (graph2 condition InternalOriginalStepGuard.one input parameter)) at ha
  change Nonempty (Derivation body Delta (graph2 (InternalAcceptance.branch C R S) out input parameter)) at hr
  apply programCases C (Fin.cons input (Fin.cons parameter Fin.elim0)) _
  intro beta j Theta control hj hc
  simp only [iffRename,graph3Rename]
  have hc' : Nonempty (Derivation body Theta
      (graph2 C control (input.relabel j) (parameter.relabel j))) := by
    simpa only [graph2,consTermRename,emptyRename] using hc
  have ha' := renameInto ha j Theta hj
  simp only [graph2Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel] at ha'
  have hr' := renameInto hr j Theta hj
  rw [graph2Rename] at hr'
  have hRange' := renameInto hRange j Theta hj
  rw [rangeRename] at hRange'
  let xs : Fin 2 → InternalGraphComposition.OTerm beta := ![input.relabel j,parameter.relabel j]
  apply formulaCases (eqn control z)
  · let A := eqn control z
    have hz := outputTransport C control z xs
      (show Nonempty (Derivation body (A :: Theta) A) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
      (withHyp hc' A)
    have ho := zeroBranchElim C R S (out.relabel j) xs hz (withHyp hr' A)
    exact hR body beta (A :: Theta) (out.relabel j) (input.relabel j)
      (parameter.relabel j) (mark.relabel j) (cutoff.relabel j)
      (withHyp hRange' A) (withHyp ha' A) ho
  · let A := (eqn control z).not
    have ho := nonzeroBranchElim C R S (out.relabel j) control xs (withHyp hc' A)
      (show Nonempty (Derivation body (A :: Theta) A) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
      (withHyp hr' A)
    exact hS body beta (A :: Theta) (out.relabel j) (input.relabel j)
      (parameter.relabel j) (mark.relabel j) (cutoff.relabel j)
      (withHyp hRange' A) (withHyp ha' A) ho

theorem observedPreservation (condition active : Program 2) (mark : Program 1)
    (previous : Program 2) (observer : Program 3)
    (hPrevious : Keeps condition previous observer) :
    Keeps condition
      (OriginalApplicationSidecarTransitionPipelineDefinitions.observed active mark previous) observer :=
  branchPreservation condition active previous _ observer hPrevious
    (branchPreservation condition _ (.projection 0) previous observer
      (projectionPreservation condition observer) hPrevious)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverWrapperProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverWrapperProof
