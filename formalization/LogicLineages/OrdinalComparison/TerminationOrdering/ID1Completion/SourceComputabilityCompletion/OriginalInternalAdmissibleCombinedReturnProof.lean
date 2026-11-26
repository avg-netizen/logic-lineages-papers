module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAdmissibleCombinedReturnTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAdmissibleReturnProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalReturnCombinedControlProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAdmissibleCombinedReturnProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open GuardedSourceSyntaxProof (numeralRename)
theorem actualReturn : OriginalInternalAdmissibleCombinedReturnTargets.ActualReturn := by
 intro R body H M W alpha Delta input work results frame rest payload parent counts role typed typ rawJob raw parameter c gamma psi
   hs hw hf hp hpar hty hr hpctx ha next
 apply OriginalInternalAdmissibleReturnProof.actualReturn R body H M W alpha Delta input work results frame rest payload parent counts role typed typ rawJob raw parameter c gamma psi
   hs hw hf hp hpar hty hr hpctx ha
 intro beta j Theta output stack hj hpair hstep
 have hs' := renameInto hs j Theta hj
 have hw' := renameInto hw j Theta hj
 have hf' := renameInto hf j Theta hj
 simp only [graph2Rename,numeralRename] at hs' hw' hf'
 exact next beta j Theta output stack hj hpair
  (OriginalInternalReturnCombinedControlProof.control R (input.relabel j) (work.relabel j) (results.relabel j) (frame.relabel j) (rest.relabel j) (payload.relabel j) output hs' hw' hf' hstep)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAdmissibleCombinedReturnProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAdmissibleCombinedReturnProof
