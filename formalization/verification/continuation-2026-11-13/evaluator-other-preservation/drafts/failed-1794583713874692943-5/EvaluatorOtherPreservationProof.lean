module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorOtherPreservationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyOtherLeafProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorOtherPreservationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof
open InternalAcceptanceSupportProof (programCases)
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open Context.EvaluatorKeyPut
open EvaluatorErasureSyntax
/-- The selected OTHER output is the actual accepted minimum, so its domain
and unchanged evaluator fibre follow from the actual minimum-hit theorem. -/
theorem actualOtherPreservation : EvaluatorOtherPreservationTargets.ActualOtherPreservation := by
 intro p H G W P body alpha Delta input output parameter
 dsimp only
 intro hd ho hl
 let Min := (minimumInputs p H G W P).base.oldRepresentative
 apply programCases Min (Fin.cons input (Fin.cons parameter Fin.elim0)) _
 intro beta j Theta minimum hj hm
 have hd' := renameInto hd j Theta hj
 have ho' := renameInto ho j Theta hj
 have hl' := renameInto hl j Theta hj
 simp only [Domain,OriginalActiveKernelMinimumSupportProof.domainRename] at hd'
 simp only [graph1Rename,sucRelabel,zRelabel] at ho'
 rw [graph2Rename] at hl'
 simp only [consTermRename,emptyRename] at hm
 obtain ⟨he⟩ := Context.EvaluatorKeyOtherLeafProof.outputIsMinimum p H G W P
   (input.relabel j) (output.relabel j) minimum (parameter.relabel j) hd' hm ho' hl'
 have hout := outputTransport Min minimum (output.relabel j)
   (Fin.cons (input.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0))
   ⟨InternalTagArithmeticSupportProof.symm he⟩ hm
 have hh := Context.EvaluatorKeyOtherMinimumProof.minimumHit p H G W P
   (input.relabel j) (output.relabel j) (parameter.relabel j) hd' hout
 simpa only [conjunctionRename,Domain,OriginalActiveKernelMinimumSupportProof.domainRename,Same,sameRename] using hh
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorOtherPreservationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorOtherPreservationProof
