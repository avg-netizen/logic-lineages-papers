module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyFinalOutputDomainTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalDomainProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyFinalFoldProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyObjectSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyFinalOutputDomainProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andIntro)
open InternalAcceptanceSupportProof (programCases)
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof
open UniformCertificateCompletion EvaluatorKeyPut
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
attribute [local irreducible] programGraph

theorem actualFinalFoldDomain : EvaluatorKeyFinalOutputDomainTargets.ActualFinalFoldDomain := by
  intro p H G W P body alpha Delta input out parameter hd hf
  exact EvaluatorKeyCanonicalDomainProof.actualCanonicalDomain p H G W P body alpha Delta input out parameter hd
    (EvaluatorKeyFinalFoldProof.toCanonical p H G W P out input parameter hd hf)

theorem actualObjectDomain : EvaluatorKeyFinalOutputDomainTargets.ActualObjectDomain := by
  intro p H G W P body alpha Delta context inputObject outputObject gamma raw outRaw parameter hp hparam hd ho hr
  apply programCases (EvaluatorKeyFinalFoldDefinitions.fold p H G W P)
    (Fin.cons raw (Fin.cons parameter Fin.elim0)) _
  intro beta j Theta actualRaw hj hf
  simp only [conjunctionRename,Domain,OriginalActiveKernelMinimumSupportProof.domainRename,graph2Rename]
  have hp' := renameInto hp j Theta hj
  have hparam' := renameInto hparam j Theta hj
  have hd' := renameInto hd j Theta hj
  have ho' := renameInto ho j Theta hj
  have hr' := renameInto hr j Theta hj
  rw [graph2Rename] at hp' hparam' ho'
  rw [graph1Rename] at hr'
  simp only [Domain,OriginalActiveKernelMinimumSupportProof.domainRename] at hd'
  simp only [consTermRename,emptyRename] at hf
  have hpair := EvaluatorKeyObjectSupportProof.outputPair (refined p H G W P)
    (context.relabel j) (inputObject.relabel j) (outputObject.relabel j) (gamma.relabel j)
    (raw.relabel j) (parameter.relabel j) actualRaw hp' hparam' hf ho'
  have he := valueUnique InternalUnpair.right actualRaw (outRaw.relabel j) (![outputObject.relabel j])
    (pairRight (outputObject.relabel j) (gamma.relabel j) actualRaw hpair) hr'
  have hfold := outputTransport (EvaluatorKeyFinalFoldDefinitions.fold p H G W P) actualRaw (outRaw.relabel j)
    (Fin.cons (raw.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)) he hf
  have hout := actualFinalFoldDomain p H G W P body beta Theta
    (raw.relabel j) (outRaw.relabel j) (parameter.relabel j) hd' hfold
  have hpaired := reconstructPair (outputObject.relabel j) (gamma.relabel j) (outRaw.relabel j)
    (pairLeft (outputObject.relabel j) (gamma.relabel j) actualRaw hpair) hr'
  exact andIntro hout hpaired
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyFinalOutputDomainProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyFinalOutputDomainProof
