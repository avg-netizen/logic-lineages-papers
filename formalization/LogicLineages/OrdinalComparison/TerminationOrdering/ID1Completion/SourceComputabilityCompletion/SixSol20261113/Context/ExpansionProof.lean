module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ExpansionSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ExpansionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeel (graph5)
open InternalApplicationStepPeelSupportProof (graph5Rename andIntro)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalRecursionGraphSyntaxProof
open InternalTagArithmeticSyntaxProof (z zRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalContextInsertion (lengthGraph)
open OriginalContextInsertionSyntaxProof (lengthRename)
open SixSol20261112.Context ExpansionSupportProof

theorem actualExpansionSplit : ExpansionTargets.ActualExpansionSplit := by
  intro arity body alpha Delta typ raw parameter window gamma rawJob tagged job front suffix jobs annotatedFront mapped full hparam hr ht hj ha hc hd happ hp hm hf
  have hraw := rawExpansion raw parameter front suffix jobs hc hd happ
  have hdec := decorateRecover typ raw parameter rawJob tagged job jobs full hr ht hj hraw hf
  apply programCases OriginalContextInsertion.length (Fin.cons suffix Fin.elim0) _
  intro beta rho Theta count hinc hcount
  rw [graph2Rename]
  have ha' := renameInto ha rho Theta hinc
  have hc' := renameInto hc rho Theta hinc
  have happ' := renameInto happ rho Theta hinc
  have hp' := renameInto hp rho Theta hinc
  have hm' := renameInto hm rho Theta hinc
  have hdec' := renameInto hdec rho Theta hinc
  simp only [graph1Rename,graph2Rename,graph4Rename,graph5Rename,zRelabel,
    GuardedSourceSyntaxProof.numeralRename] at ha' hc' happ' hp' hm' hdec'
  simp only [consTermRename,emptyRename] at hcount
  exact splitAtLength arity (typ.relabel rho) (raw.relabel rho) (parameter.relabel rho)
    (front.relabel rho) (suffix.relabel rho) (jobs.relabel rho) (annotatedFront.relabel rho)
    count (mapped.relabel rho) (full.relabel rho) ha' hc' happ' hp' hcount hm' hdec'

theorem actualExpansionDeletionRow : ExpansionTargets.ActualExpansionDeletionRow := by
  intro Q arity body alpha Delta input typ raw parameter window gamma rawJob tagged job front suffix jobs annotatedFront mapped full row hi hparam hr ht hj ha hc hd happ hp hm hf
  exact andIntro
    (actualExpansionSplit arity body alpha Delta typ raw parameter window gamma rawJob tagged job
      front suffix jobs annotatedFront mapped full hparam hr ht hj ha hc hd happ hp hm hf)
    (InheritedMapProof.actualInheritedDeletionRow Q body alpha Delta input typ raw parameter suffix mapped row hi hd hm)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ExpansionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ExpansionProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ExpansionProof.actualExpansionSplit
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ExpansionProof.actualExpansionDeletionRow
