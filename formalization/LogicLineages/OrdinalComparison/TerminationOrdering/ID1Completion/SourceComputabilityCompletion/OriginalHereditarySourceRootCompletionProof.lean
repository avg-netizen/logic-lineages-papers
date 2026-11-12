module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditarySourceRootCompletionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRootPotentialProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInitialBranchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryPotentialActualCompletionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditarySourceRootCompletionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro)
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalAcceptanceSupportProof (programCases)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalControlGraphSupportProof (emptyRename)
open OriginalHereditaryPotentialCompletionSyntaxProof (emptyRename)
open GuardedSourceSyntaxProof (numeralRename)
open SourceComputabilityFormulaSupportProof (numeral)
theorem actualSourceRootCompletion : OriginalHereditarySourceRootCompletionTargets.ActualSourceRootCompletion := by
 intro R body H G M W alpha Delta packed parameter typ raw gamma c rawJob typed job B visit work fuel initial output
   hp hc hr ht hj hs hb hf hv hw hi hrun
 apply programCases OriginalHereditaryFuelProgram.weight (Fin.cons job Fin.elim0) _
 intro beta j Theta weight hinc hweight
 rw [OriginalHereditaryPotentialCompletionSyntaxProof.emptyRename]
 simp only [consTermRename,InternalControlGraphSupportProof.emptyRename] at hweight
 have hp' := renameInto hp j Theta hinc
 have hc' := renameInto hc j Theta hinc
 have hr' := renameInto hr j Theta hinc
 have ht' := renameInto ht j Theta hinc
 have hj' := renameInto hj j Theta hinc
 have hs' := renameInto hs j Theta hinc
 have hb' := renameInto hb j Theta hinc
 have hf' := renameInto hf j Theta hinc
 have hv' := renameInto hv j Theta hinc
 have hw' := renameInto hw j Theta hinc
 have hi' := renameInto hi j Theta hinc
 have hrun' := renameInto hrun j Theta hinc
 simp only [graph1Rename,graph2Rename,numeralRename] at hp' hc' hr' ht' hj' hs' hb' hf' hv' hw' hi' hrun'
 have hagenda := OriginalHereditaryInitialBranchProof.actualAgenda body H G M W beta Theta
   (packed.relabel j) (parameter.relabel j) (typ.relabel j) (raw.relabel j) (gamma.relabel j) (c.relabel j)
   (rawJob.relabel j) (typed.relabel j) (job.relabel j) weight (B.relabel j) (visit.relabel j) (work.relabel j)
   hp' hc' hr' ht' hj' hs' hweight hb' hv' hw'
 have hpotential := OriginalHereditaryRootPotentialProof.actualInitialPotential body beta Theta
   (job.relabel j) (visit.relabel j) (work.relabel j) (B.relabel j) (fuel.relabel j) hv' hw' hb' hf'
 exact OriginalHereditaryPotentialActualCompletionProof.actualCompletion R H M W body beta Theta
   (c.relabel j) (B.relabel j) (fuel.relabel j) (initial.relabel j) (work.relabel j) (numeral 0) (fuel.relabel j) (output.relabel j)
   (andIntro hi' (andIntro hagenda (andIntro hpotential (andIntro (InternalCoprimeMultipleBoundedProof.selfLtSucc _) hrun'))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditarySourceRootCompletionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditarySourceRootCompletionProof
