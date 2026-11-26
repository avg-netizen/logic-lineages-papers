module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.SourceRootProjectionSupport
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAgendaVisitProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.SourceRootInitialProjection
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
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem atVisit (R : Program 2) (H : Program 1) (M W : Program 2)
 (c B packed parameter typ raw rawJob typed job visit work initial count jobs output outWork stack value old root tail : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed typ raw)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawJob)))
 (hj : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job z typed)))
 (hv : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing visit z job)))
 (hw : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work visit z)))
 (hi : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing initial work z)))
 (ha : Nonempty (Derivation body Delta (Agenda H M W c B work)))
 (hexp : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.expansion jobs job)))
 (hrun : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryRuntimeIterationDefinitions.run R) output (suc count) initial)))
 (he : Nonempty (Derivation body Delta (OriginalHereditaryPotentialCompletion.Empty output)))
 (hout : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing output outWork stack)))
 (hstack : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode stack value old)))
 (hvalue : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing value root tail))) :
 Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation R) root packed parameter)) := by
 have hvisit := OriginalHereditaryInternalVisitProof.visitCases R body alpha Delta
   initial work z visit z job jobs (graph2 (OriginalRootObservation.rootObservation R) root packed parameter)
 simp only [SourceRootProjectionSupport.zeroEq] at hvisit
 apply hvisit hi hw hv hexp
 intro beta j Theta childCount deletionCount counts payload frame tagged returnRest nextWork next
   hinc _ _ _ hpay hframe htag hreturnRest hscheduled hnext hstep
 simp only [numeralRename,InternalTagArithmeticSyntaxProof.zRelabel] at hreturnRest hnext
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
 have hout' := renameInto hout j Theta hinc
 have hstack' := renameInto hstack j Theta hinc
 have hvalue' := renameInto hvalue j Theta hinc
 simp only [graph1Rename,graph2Rename,numeralRename,InternalTagArithmeticSyntaxProof.zRelabel,agendaRename,sucRelabel,OriginalHereditaryPotentialCompletionSyntaxProof.emptyRename]
   at hp' hr' ht' hj' hv' hw' ha' hexp' hrun' he' hout' hstack' hvalue'
 have hpreserve := OriginalHereditaryInternalAgendaVisitProof.actualVisitPreservation body beta Theta H M W
   (c.relabel j) (B.relabel j) (work.relabel j) (visit.relabel j) z (job.relabel j) (jobs.relabel j)
   tagged counts payload frame returnRest nextWork
 simp only [SourceRootProjectionSupport.zeroEq] at hpreserve
 have hnewAgenda := hpreserve ha' hw' hv' hexp' htag hpay hframe hreturnRest hscheduled
 have htail := InternalNumericIterationProof.frontSuccForward (OriginalHereditaryCombinedStep.step R)
   (count.relabel j) (output.relabel j) (initial.relabel j) next hstep hrun'
 rw [graph2Rename]
 exact SuffixExitProof.actualExit R H M W body beta Theta (c.relabel j) (B.relabel j)
   returnRest (output.relabel j) (count.relabel j) next nextWork z tagged
   (graph2 (OriginalRootObservation.rootObservation R) (root.relabel j) (packed.relabel j) (parameter.relabel j))
   hnext hnewAgenda hscheduled htail he'
   (SourceRootProjectionSupport.suffixConsumer R returnRest frame payload (job.relabel j) counts (typed.relabel j)
     (typ.relabel j) (rawJob.relabel j) (raw.relabel j) (parameter.relabel j) (packed.relabel j)
     (output.relabel j) (outWork.relabel j) (stack.relabel j) (value.relabel j) (old.relabel j) (root.relabel j) (tail.relabel j)
     hreturnRest hframe hpay hj' ht' hr' hp' hout' hstack' hvalue')

theorem positive (R : Program 2) (H : Program 1) (M W : Program 2)
 (c B packed parameter typ raw rawJob typed job visit work initial count output outWork stack value old root tail : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed typ raw)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawJob)))
 (hj : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job z typed)))
 (hv : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing visit z job)))
 (hw : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work visit z)))
 (hi : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing initial work z)))
 (ha : Nonempty (Derivation body Delta (Agenda H M W c B work)))
 (hrun : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryRuntimeIterationDefinitions.run R) output (suc count) initial)))
 (he : Nonempty (Derivation body Delta (OriginalHereditaryPotentialCompletion.Empty output)))
 (hout : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing output outWork stack)))
 (hstack : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode stack value old)))
 (hvalue : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing value root tail))) :
 Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation R) root packed parameter)) := by
 apply programCases OriginalHereditaryAnnotatedExpansion.expansion (Fin.cons job Fin.elim0) _
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
 have hout' := renameInto hout j Theta hinc
 have hstack' := renameInto hstack j Theta hinc
 have hvalue' := renameInto hvalue j Theta hinc
 simp only [graph1Rename,graph2Rename,numeralRename,InternalTagArithmeticSyntaxProof.zRelabel,agendaRename,sucRelabel,OriginalHereditaryPotentialCompletionSyntaxProof.emptyRename]
   at hp' hr' ht' hj' hv' hw' hi' ha' hrun' he' hout' hstack' hvalue'
 rw [graph2Rename]
 exact atVisit R H M W (c.relabel j) (B.relabel j) (packed.relabel j) (parameter.relabel j) (typ.relabel j)
   (raw.relabel j) (rawJob.relabel j) (typed.relabel j) (job.relabel j) (visit.relabel j) (work.relabel j) (initial.relabel j)
   (count.relabel j) jobs (output.relabel j) (outWork.relabel j) (stack.relabel j) (value.relabel j) (old.relabel j) (root.relabel j) (tail.relabel j)
   hp' hr' ht' hj' hv' hw' hi' ha' hexp hrun' he' hout' hstack' hvalue'

theorem completed (R : Program 2) (H : Program 1) (M W : Program 2)
 (c B packed parameter typ raw rawJob typed job visit work initial fuel output outWork stack value old root tail : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed typ raw)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawJob)))
 (hj : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job z typed)))
 (hv : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing visit z job)))
 (hw : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work visit z)))
 (hi : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing initial work z)))
 (ha : Nonempty (Derivation body Delta (Agenda H M W c B work)))
 (hrun : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryRuntimeIterationDefinitions.run R) output fuel initial)))
 (he : Nonempty (Derivation body Delta (OriginalHereditaryPotentialCompletion.Empty output)))
 (hout : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing output outWork stack)))
 (hstack : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode stack value old)))
 (hvalue : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing value root tail))) :
 Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation R) root packed parameter)) := by
 apply zeroSuccessorCases Delta fuel _
 · let A := eqn fuel z
   have inc : ∀ f ∈ Delta, f ∈ A :: Delta := fun f hf => List.mem_cons_of_mem _ hf
   have hzero := headTransport (OriginalHereditaryRuntimeIterationDefinitions.run R) output fuel z (Fin.cons initial Fin.elim0)
     ⟨Derivation.hypothesis List.mem_cons_self⟩ (weakenProof hrun inc)
   have heq := InternalNumericIterationSupportProof.repeatZeroRecover (OriginalHereditaryCombinedStep.step R) output initial hzero
   have hempty := headTransport InternalUnpair.left z output initial Fin.elim0 heq (weakenProof he inc)
   exact SuffixExitCore.emptyContradiction initial work z visit z _ (weakenProof hi inc) (weakenProof hw inc) hempty
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
   have hout' := renameInto hout j Theta hinc
   have hstack' := renameInto hstack j Theta hinc
   have hvalue' := renameInto hvalue j Theta hinc
   simp only [graph1Rename,graph2Rename,numeralRename,InternalTagArithmeticSyntaxProof.zRelabel,agendaRename,OriginalHereditaryPotentialCompletionSyntaxProof.emptyRename]
     at hp' hr' ht' hj' hv' hw' hi' ha' hrun' he' hout' hstack' hvalue'
   have hsucc := headTransport (OriginalHereditaryRuntimeIterationDefinitions.run R) (output.relabel j)
     (fuel.relabel j) (suc count) (Fin.cons (initial.relabel j) Fin.elim0) hfuel hrun'
   rw [graph2Rename]
   exact positive R H M W (c.relabel j) (B.relabel j) (packed.relabel j) (parameter.relabel j) (typ.relabel j)
     (raw.relabel j) (rawJob.relabel j) (typed.relabel j) (job.relabel j) (visit.relabel j) (work.relabel j) (initial.relabel j)
     count (output.relabel j) (outWork.relabel j) (stack.relabel j) (value.relabel j) (old.relabel j) (root.relabel j) (tail.relabel j)
     hp' hr' ht' hj' hv' hw' hi' ha' hsucc he' hout' hstack' hvalue'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.SourceRootInitialProjection
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.SourceRootInitialProjection
