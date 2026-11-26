module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalDomainSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalDomainProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalAcceptanceSupportProof (programCases)
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof
open InternalControlGraphSupportProof (emptyRename)
open EvaluatorKeyPut

theorem actualCanonicalDomain : EvaluatorKeyCanonicalDomainTargets.ActualCanonicalDomain := by
  intro p H G W P body alpha Delta input out parameter hd hc
  apply programCases InternalUnpair.left (Fin.cons input Fin.elim0) _
  intro beta j Theta typ hj ht
  simp only [Domain,OriginalActiveKernelMinimumSupportProof.domainRename]
  have hd' := renameInto hd j Theta hj
  simp only [Domain,OriginalActiveKernelMinimumSupportProof.domainRename] at hd'
  have hc' := renameInto hc j Theta hj
  rw [graph2Rename] at hc'
  simp only [consTermRename,emptyRename] at ht
  exact EvaluatorKeyCanonicalDomainSupportProof.atType p H G W P
    (input.relabel j) (out.relabel j) (parameter.relabel j) typ hd' hc' ht
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalDomainProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalDomainProof
