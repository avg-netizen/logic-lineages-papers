module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.SourceRootInitialProjection
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditarySourceRootCompletionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.SourceRootProjectionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
theorem actualSourceRootProjection : SourceRootProjectionTargets.ActualSourceRootProjection := by
 intro R body H G M W alpha Delta packed parameter typ raw gamma c rawJob typed job B visit work fuel initial output outWork stack value old root tail
   hp hc hr ht hj hs hb hf hv hw hi hrun hout hstack hvalue
 have hempty := OriginalHereditarySourceRootCompletionProof.actualSourceRootCompletion R body H G M W alpha Delta
   packed parameter typ raw gamma c rawJob typed job B visit work fuel initial output
   hp hc hr ht hj hs hb hf hv hw hi hrun
 apply programCases OriginalHereditaryFuelProgram.weight (Fin.cons job Fin.elim0) _
 intro beta j Theta weight hinc hweight
 simp only [consTermRename,emptyRename] at hweight
 have hp' := renameInto hp j Theta hinc
 have hc' := renameInto hc j Theta hinc
 have hr' := renameInto hr j Theta hinc
 have ht' := renameInto ht j Theta hinc
 have hj' := renameInto hj j Theta hinc
 have hs' := renameInto hs j Theta hinc
 have hb' := renameInto hb j Theta hinc
 have hv' := renameInto hv j Theta hinc
 have hw' := renameInto hw j Theta hinc
 have hi' := renameInto hi j Theta hinc
 have hrun' := renameInto hrun j Theta hinc
 have hempty' := renameInto hempty j Theta hinc
 have hout' := renameInto hout j Theta hinc
 have hstack' := renameInto hstack j Theta hinc
 have hvalue' := renameInto hvalue j Theta hinc
 simp only [graph1Rename,graph2Rename,numeralRename,OriginalHereditaryPotentialCompletionSyntaxProof.emptyRename]
   at hp' hc' hr' ht' hj' hs' hb' hv' hw' hi' hrun' hempty' hout' hstack' hvalue'
 have hagenda := OriginalHereditaryInitialBranchProof.actualAgenda body H G M W beta Theta
   (packed.relabel j) (parameter.relabel j) (typ.relabel j) (raw.relabel j) (gamma.relabel j) (c.relabel j)
   (rawJob.relabel j) (typed.relabel j) (job.relabel j) weight (B.relabel j) (visit.relabel j) (work.relabel j)
   hp' hc' hr' ht' hj' hs' hweight hb' hv' hw'
 rw [graph2Rename]
 exact SourceRootInitialProjection.completed R H M W (c.relabel j) (B.relabel j) (packed.relabel j) (parameter.relabel j)
   (typ.relabel j) (raw.relabel j) (rawJob.relabel j) (typed.relabel j) (job.relabel j) (visit.relabel j)
   (work.relabel j) (initial.relabel j) (fuel.relabel j) (output.relabel j) (outWork.relabel j) (stack.relabel j)
   (value.relabel j) (old.relabel j) (root.relabel j) (tail.relabel j)
   hp' hr' ht' hj' hv' hw' hi' hagenda hrun' hempty' hout' hstack' hvalue'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.SourceRootProjectionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.SourceRootProjectionProof
