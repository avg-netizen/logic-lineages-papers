module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryPotentialCompletionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAdmissibleCombinedReturnProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAgendaStructuralProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAgendaTransportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaPotentialReturnProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAnnotationEqualityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryPotentialStepReturnProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalTagArithmeticSyntaxProof (eqn z suc)
open InternalTagArithmeticSupportProof (symm)
open InternalOriginalOrderSyntaxProof (ltF orderRename)
open InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open GuardedSourceSyntaxProof (numeralRename)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalHereditaryInternalAgenda OriginalHereditaryInternalAgendaSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem returnProgress (R : Program 2) (H : Program 1) (M W : Program 2)
 (c B input work results before next nextWork nextResults after frame rest payload parent counts
 role typ typed rawJob raw parameter gamma weight : OTerm alpha)
 (hs : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input work results)))
 (ha : Nonempty (Derivation body Delta (Agenda H M W c B work)))
 (hb : Nonempty (Derivation body Delta (graph2 OriginalHereditaryAgendaPotential.agenda before work B)))
 (hn : Nonempty (Derivation body Delta (graph1 (OriginalHereditaryCombinedStep.step R) next input)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing next nextWork nextResults)))
 (hm : Nonempty (Derivation body Delta (graph2 OriginalHereditaryAgendaPotential.agenda after nextWork B)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work frame rest)))
 (hf : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (numeral 1) payload)))
 (hpay : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload parent counts)))
 (hj : Nonempty (Derivation body Delta (jobFields H M W c B parent role typ typed rawJob raw parameter gamma weight))) :
 Nonempty (Derivation body Delta (Agenda H M W c B nextWork ⊓ ltF after before)) := by
 apply OriginalInternalAdmissibleCombinedReturnProof.actualReturn R body H M W alpha Delta
   input work results frame rest payload parent counts role typed typ rawJob raw parameter c gamma _
   hs hc hf hpay (andLeft hj) (andLeft (andRight hj)) (andLeft (andRight (andRight hj)))
   (andLeft (andRight (andRight (andRight hj)))) (andLeft (andRight (andRight (andRight (andRight hj)))))
 intro beta j Theta output stack hinc hpair hstep
 simp only [conjunctionRename,agendaRename,orderRename]
 have ha' := renameInto ha j Theta hinc
 have hb' := renameInto hb j Theta hinc
 have hn' := renameInto hn j Theta hinc
 have hp' := renameInto hp j Theta hinc
 have hm' := renameInto hm j Theta hinc
 have hc' := renameInto hc j Theta hinc
 have hf' := renameInto hf j Theta hinc
 simp only [graph1Rename,graph2Rename,agendaRename,numeralRename] at ha' hb' hn' hp' hm' hc' hf'
 have he := valueUnique (OriginalHereditaryCombinedStep.step R) (next.relabel j) output (Fin.cons (input.relabel j) Fin.elim0) hn' hstep
 have hfields := OriginalInternalAnnotationEqualityProof.pairFields (next.relabel j) output (nextWork.relabel j) (nextResults.relabel j) (rest.relabel j) stack hp' hpair he
 have hwEq := andLeft hfields
 have hafter := headTransport OriginalHereditaryAgendaPotential.agenda (after.relabel j) (nextWork.relabel j) (rest.relabel j) (Fin.cons (B.relabel j) Fin.elim0) hwEq hm'
 have hdrop := OriginalHereditaryAgendaPotentialReturnProof.actualReturnPop body beta Theta
   (frame.relabel j) (payload.relabel j) (work.relabel j) (rest.relabel j) (B.relabel j) (before.relabel j) (after.relabel j) hf' hc' hb' hafter
 have htail := OriginalHereditaryInternalAgendaStructuralProof.tail H M W (c.relabel j) (B.relabel j) (work.relabel j) (frame.relabel j) (rest.relabel j) ha' hc'
 obtain ⟨hwEq⟩ := hwEq
 have hinv := OriginalHereditaryInternalAgendaTransportProof.agendaTransport H M W (c.relabel j) (B.relabel j) (rest.relabel j) (nextWork.relabel j)
  (by simpa only [equalEqn] using (Nonempty.intro (symm hwEq))) htail
 exact andIntro hinv hdrop
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryPotentialStepReturnProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryPotentialStepReturnProof
