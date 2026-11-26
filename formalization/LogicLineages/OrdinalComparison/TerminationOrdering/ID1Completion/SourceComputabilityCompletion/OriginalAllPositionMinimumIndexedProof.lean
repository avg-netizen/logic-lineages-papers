module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionMinimumIndexedTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextAllPositionSelectionOutputProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverRangeSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportLogicalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionMinimumIndexedProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (suc z)
open InternalOriginalOrderSyntaxProof (orderRename)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open OriginalTypedDecoderTransportLogicalProof (iffRename)
open OriginalIndexedObserverDefinitions OriginalIndexedObserverRangeSyntaxProof
open OriginalAllPositionMinimumIndexed OriginalAllPositionMinimumIndexedTargets
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem atCount (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
    (out input parameter indicator cutoff count : InternalGraphComposition.OTerm alpha)
    (ha : Nonempty (Derivation body Delta
      (graph2 (OriginalActiveClassKernel.domainProgram p H G W) InternalOriginalStepGuard.one input parameter)))
    (hl : Nonempty (Derivation body Delta (graph1 contextLength count parameter)))
    (hb : Nonempty (Derivation body Delta (OriginalContextInsertion.Below cutoff count)))
    (hr : Nonempty (Derivation body Delta
      (graph2 (OriginalClassContextAllPositionSelection.inputs p H G W P).base.oldRepresentative out input parameter))) :
    Nonempty (Derivation body Delta
      ((graph3 (OriginalClassContextAllPositionObserver.positionObservation p.base.oldRepresentative)
        indicator cutoff out parameter).iff
       (graph3 (OriginalClassContextAllPositionObserver.positionObservation p.base.oldRepresentative)
        indicator cutoff input parameter))) := by
  apply programCases InternalUnpair.right (Fin.cons parameter Fin.elim0) _
  intro beta j Theta gamma hj hg
  simp only [iffRename,graph3Rename]
  have ha' := renameInto ha j Theta hj
  have hl' := renameInto hl j Theta hj
  have hb' := renameInto hb j Theta hj
  have hr' := renameInto hr j Theta hj
  simp only [graph2Rename,InternalOriginalStepGuard.one,InternalTagArithmeticSyntaxProof.sucRelabel,
    InternalTagArithmeticSyntaxProof.zRelabel] at ha'
  simp only [graph1Rename] at hl'
  change Nonempty (Derivation body Theta ((InternalOriginalOrderSyntaxProof.ltF cutoff count).relabel j)) at hb'
  rw [orderRename] at hb'
  simp only [graph2Rename] at hr'
  simp only [consTermRename,emptyRename] at hg
  have hlength : Nonempty (Derivation body Theta
      (OriginalContextInsertion.lengthGraph (count.relabel j) gamma)) := by
    apply compositionRecover OriginalContextInsertion.length (fun _ : Fin 1 => InternalUnpair.right)
      (count.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0) (Fin.cons gamma Fin.elim0) hl'
    intro i
    obtain rfl := Fin.eq_zero i
    exact hg
  obtain ⟨ho⟩ := OriginalClassContextAllPositionSelectionOutputProof.outputAt p H G W P
    (input.relabel j) (out.relabel j) (parameter.relabel j) gamma (count.relabel j)
    (cutoff.relabel j) (indicator.relabel j)
    (OriginalActiveClassKernelBranchProof.domainRecover p H G W (input.relabel j) (parameter.relabel j) ha')
    hg hlength hb' hr'
  exact ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionRight ho) (Derivation.conjunctionLeft ho)⟩

theorem actualPreservation : ActualPreservation := by
  intro p H G W P body alpha Delta out input parameter indicator cutoff hRange ha hr
  change Nonempty (Derivation body Delta
    ((graph3 (OriginalClassContextAllPositionObserver.positionObservation p.base.oldRepresentative)
      indicator cutoff out parameter).iff
     (graph3 (OriginalClassContextAllPositionObserver.positionObservation p.base.oldRepresentative)
      indicator cutoff input parameter)))
  apply rangeCases cutoff parameter _ hRange
  intro beta j Theta count hj hc
  simp only [iffRename,graph3Rename]
  have ha' := renameInto ha j Theta hj
  have hr' := renameInto hr j Theta hj
  change Nonempty (Derivation body Theta
    ((graph2 (OriginalActiveClassKernel.domainProgram p H G W) InternalOriginalStepGuard.one input parameter).relabel j)) at ha'
  change Nonempty (Derivation body Theta
    ((graph2 (OriginalClassContextAllPositionSelection.inputs p H G W P).base.oldRepresentative out input parameter).relabel j)) at hr'
  simp only [graph2Rename,InternalOriginalStepGuard.one,InternalTagArithmeticSyntaxProof.sucRelabel,
    InternalTagArithmeticSyntaxProof.zRelabel] at ha'
  simp only [graph2Rename] at hr'
  exact atCount p H G W P (out.relabel j) (input.relabel j) (parameter.relabel j)
    (indicator.relabel j) (cutoff.relabel j) count ha' (andLeft hc) (andRight hc) hr'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionMinimumIndexedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionMinimumIndexedProof
