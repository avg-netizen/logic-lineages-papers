module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.RootResultConsumerProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAgendaVisitProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.RootResultInitialProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalTagArithmeticSyntaxProof (z suc eqn sucRelabel)
open InternalApplicationValidityStackAppendFrameQueryProof (weakenProof)
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedSourceSyntaxProof (numeralRename)
open OriginalHereditaryPotentialCompletionSyntaxProof (emptyRename)
open OriginalHereditaryInternalAgenda OriginalHereditaryInternalAgendaSyntaxProof
open RootResultDefinitions
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem atVisit (R : Program 2) (H : Program 1) (M W : Program 2)
 (c B packed parameter typ raw rawJob typed job visit work initial count jobs output : OTerm alpha) (psi : Formula alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed typ raw)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawJob)))
 (hj : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job (numeral 0) typed)))
 (hv : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing visit (numeral 0) job)))
 (hw : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work visit (numeral 0))))
 (hi : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing initial work (numeral 0))))
 (ha : Nonempty (Derivation body Delta (Agenda H M W c B work)))
 (hexp : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.expansion jobs job)))
 (hrun : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryRuntimeIterationDefinitions.run R) output (suc count) initial)))
 (he : Nonempty (Derivation body Delta (OriginalHereditaryPotentialCompletion.Empty output)))
 (next : ReturnConsumer R body Delta packed parameter output psi) : Nonempty (Derivation body Delta psi) := by
 apply OriginalHereditaryInternalVisitProof.visitCases R body alpha Delta
   initial work (numeral 0) visit (numeral 0) job jobs psi hi hw hv hexp
 intro beta j Theta childCount deletionCount counts payload frame tagged returnRest nextWork step
   hinc _ _ _ hpay hframe htag hreturnRest hscheduled hstepState hstep
 simp only [numeralRename] at hreturnRest hstepState
 have hp' := renameInto hp j Theta hinc
 have hr' := renameInto hr j Theta hinc
 have ht' := renameInto ht j Theta hinc
 have hj' := renameInto hj j Theta hinc
 have hv' := renameInto hv j Theta hinc
 have hw' := renameInto hw j Theta hinc
 have ha' := renameInto ha j Theta hinc
 have hexp' := renameInto hexp j Theta hinc
 have hrun' := renameInto hrun j Theta hinc
 have he' := renameInto he j Theta hinc
 simp only [graph1Rename,graph2Rename,numeralRename,agendaRename,sucRelabel,OriginalHereditaryPotentialCompletionSyntaxProof.emptyRename]
   at hp' hr' ht' hj' hv' hw' ha' hexp' hrun' he'
 have hnewAgenda := OriginalHereditaryInternalAgendaVisitProof.actualVisitPreservation body beta Theta H M W
   (c.relabel j) (B.relabel j) (work.relabel j) (visit.relabel j) (numeral 0) (job.relabel j) (jobs.relabel j)
   tagged counts payload frame returnRest nextWork ha' hw' hv' hexp' htag hpay hframe hreturnRest hscheduled
 have htail := InternalNumericIterationProof.frontSuccForward (OriginalHereditaryCombinedStep.step R)
   (count.relabel j) (output.relabel j) (initial.relabel j) step hstep hrun'
 exact SuffixExitProof.actualExit R H M W body beta Theta (c.relabel j) (B.relabel j)
   returnRest (output.relabel j) (count.relabel j) step nextWork (numeral 0) tagged (psi.relabel j)
   hstepState hnewAgenda hscheduled htail he'
   (RootResultConsumerProof.anchorConsumer R (packed.relabel j) (parameter.relabel j) (output.relabel j)
     returnRest frame payload (job.relabel j) counts (typed.relabel j) (typ.relabel j) (rawJob.relabel j) (raw.relabel j)
     (psi.relabel j) hreturnRest hframe hpay hj' ht' hr' hp'
     (RootResultConsumerProof.renameConsumer R packed parameter output psi j Theta next hinc))

theorem positive (R : Program 2) (H : Program 1) (M W : Program 2)
 (c B packed parameter typ raw rawJob typed job visit work initial count output : OTerm alpha) (psi : Formula alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed typ raw)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawJob)))
 (hj : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job (numeral 0) typed)))
 (hv : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing visit (numeral 0) job)))
 (hw : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work visit (numeral 0))))
 (hi : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing initial work (numeral 0))))
 (ha : Nonempty (Derivation body Delta (Agenda H M W c B work)))
 (hrun : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryRuntimeIterationDefinitions.run R) output (suc count) initial)))
 (he : Nonempty (Derivation body Delta (OriginalHereditaryPotentialCompletion.Empty output)))
 (next : ReturnConsumer R body Delta packed parameter output psi) : Nonempty (Derivation body Delta psi) := by
 apply programCases OriginalHereditaryAnnotatedExpansion.expansion (Fin.cons job Fin.elim0) psi
 intro beta j Theta jobs hinc hexp
 simp only [consTermRename,InternalControlGraphSupportProof.emptyRename] at hexp
 have hp' := renameInto hp j Theta hinc
 have hr' := renameInto hr j Theta hinc
 have ht' := renameInto ht j Theta hinc
 have hj' := renameInto hj j Theta hinc
 have hv' := renameInto hv j Theta hinc
 have hw' := renameInto hw j Theta hinc
 have hi' := renameInto hi j Theta hinc
 have ha' := renameInto ha j Theta hinc
 have hrun' := renameInto hrun j Theta hinc
 have he' := renameInto he j Theta hinc
 simp only [graph1Rename,graph2Rename,numeralRename,agendaRename,sucRelabel,OriginalHereditaryPotentialCompletionSyntaxProof.emptyRename]
   at hp' hr' ht' hj' hv' hw' hi' ha' hrun' he'
 exact atVisit R H M W (c.relabel j) (B.relabel j) (packed.relabel j) (parameter.relabel j) (typ.relabel j)
   (raw.relabel j) (rawJob.relabel j) (typed.relabel j) (job.relabel j) (visit.relabel j) (work.relabel j) (initial.relabel j)
   (count.relabel j) jobs (output.relabel j) (psi.relabel j) hp' hr' ht' hj' hv' hw' hi' ha' hexp hrun' he'
   (RootResultConsumerProof.renameConsumer R packed parameter output psi j Theta next hinc)

theorem completed (R : Program 2) (H : Program 1) (M W : Program 2)
 (c B packed parameter typ raw rawJob typed job visit work initial fuel output : OTerm alpha) (psi : Formula alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed typ raw)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawJob)))
 (hj : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job (numeral 0) typed)))
 (hv : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing visit (numeral 0) job)))
 (hw : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work visit (numeral 0))))
 (hi : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing initial work (numeral 0))))
 (ha : Nonempty (Derivation body Delta (Agenda H M W c B work)))
 (hrun : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryRuntimeIterationDefinitions.run R) output fuel initial)))
 (he : Nonempty (Derivation body Delta (OriginalHereditaryPotentialCompletion.Empty output)))
 (next : ReturnConsumer R body Delta packed parameter output psi) : Nonempty (Derivation body Delta psi) := by
 apply zeroSuccessorCases Delta fuel psi
 · let A := eqn fuel z
   have inc : ∀ f ∈ Delta, f ∈ A :: Delta := fun f h => List.mem_cons_of_mem _ h
   have hzero := headTransport (OriginalHereditaryRuntimeIterationDefinitions.run R) output fuel z (Fin.cons initial Fin.elim0)
     ⟨Derivation.hypothesis List.mem_cons_self⟩ (weakenProof hrun inc)
   have heq := InternalNumericIterationSupportProof.repeatZeroRecover (OriginalHereditaryCombinedStep.step R) output initial hzero
   have hempty := headTransport InternalUnpair.left z output initial Fin.elim0 heq (weakenProof he inc)
   exact SuffixExitCore.emptyContradiction initial work (numeral 0) visit (numeral 0) psi
     (weakenProof hi inc) (weakenProof hw inc) hempty
 · intro beta j Theta count hinc hfuel
   have hp' := renameInto hp j Theta hinc
   have hr' := renameInto hr j Theta hinc
   have ht' := renameInto ht j Theta hinc
   have hj' := renameInto hj j Theta hinc
   have hv' := renameInto hv j Theta hinc
   have hw' := renameInto hw j Theta hinc
   have hi' := renameInto hi j Theta hinc
   have ha' := renameInto ha j Theta hinc
   have hrun' := renameInto hrun j Theta hinc
   have he' := renameInto he j Theta hinc
   simp only [graph1Rename,graph2Rename,numeralRename,agendaRename,OriginalHereditaryPotentialCompletionSyntaxProof.emptyRename]
     at hp' hr' ht' hj' hv' hw' hi' ha' hrun' he'
   have hsucc := headTransport (OriginalHereditaryRuntimeIterationDefinitions.run R) (output.relabel j)
     (fuel.relabel j) (suc count) (Fin.cons (initial.relabel j) Fin.elim0) hfuel hrun'
   exact positive R H M W (c.relabel j) (B.relabel j) (packed.relabel j) (parameter.relabel j) (typ.relabel j)
     (raw.relabel j) (rawJob.relabel j) (typed.relabel j) (job.relabel j) (visit.relabel j) (work.relabel j) (initial.relabel j)
     count (output.relabel j) (psi.relabel j) hp' hr' ht' hj' hv' hw' hi' ha' hsucc he'
     (RootResultConsumerProof.renameConsumer R packed parameter output psi j Theta next hinc)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.RootResultInitialProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.RootResultInitialProof
