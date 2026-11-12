module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryPotentialCompletionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAdmissibleCombinedReturnProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAgendaStructuralProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAgendaTransportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaPotentialReturnProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAnnotationEqualityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalVisitProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaPotentialVisitProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryPotentialStepVisitProof
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
/-- The only staging supplier is the separately frozen actual agenda visit
preservation. Runtime effect and numeric decrease are derived here. -/
theorem visitProgress (visitPres : OriginalHereditaryInternalAgendaTargets.VisitPreservation)
 (R : Program 2) (H : Program 1) (M W : Program 2)
 (c B input work results before next nextWork nextResults after frame rest parent jobs weight : OTerm alpha)
 (hs : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input work results)))
 (ha : Nonempty (Derivation body Delta (Agenda H M W c B work)))
 (hb : Nonempty (Derivation body Delta (graph2 OriginalHereditaryAgendaPotential.agenda before work B)))
 (hn : Nonempty (Derivation body Delta (graph1 (OriginalHereditaryCombinedStep.step R) next input)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing next nextWork nextResults)))
 (hm : Nonempty (Derivation body Delta (graph2 OriginalHereditaryAgendaPotential.agenda after nextWork B)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work frame rest)))
 (hf : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (numeral 0) parent)))
 (he : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.expansion jobs parent)))
 (hweight : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight weight parent)))
 (hbound : Nonempty (Derivation body Delta (ltF (suc (suc weight)) (suc B)))) :
 Nonempty (Derivation body Delta (Agenda H M W c B nextWork ⊓ ltF after before)) := by
 apply OriginalHereditaryInternalVisitProof.visitCases R body alpha Delta input work results frame rest parent jobs _ hs hc hf he
 intro beta j Theta childCount deletionCount counts payload returnFrame tagged returnRest newWork output hinc hchild hdel hcounts hpay hreturn htagged hreturnRest happ hpair hstep
 simp only [conjunctionRename,agendaRename,orderRename]
 have ha' := renameInto ha j Theta hinc
 have hb' := renameInto hb j Theta hinc
 have hn' := renameInto hn j Theta hinc
 have hp' := renameInto hp j Theta hinc
 have hm' := renameInto hm j Theta hinc
 have hc' := renameInto hc j Theta hinc
 have hf' := renameInto hf j Theta hinc
 have he' := renameInto he j Theta hinc
 have hweight' := renameInto hweight j Theta hinc
 have hbound' := renameInto hbound j Theta hinc
 simp only [graph1Rename,graph2Rename,agendaRename,numeralRename,orderRename,InternalTagArithmeticSyntaxProof.sucRelabel] at ha' hb' hn' hp' hm' hc' hf' he' hweight' hbound'
 have heq := valueUnique (OriginalHereditaryCombinedStep.step R) (next.relabel j) output (Fin.cons (input.relabel j) Fin.elim0) hn' hstep
 have hfields := OriginalInternalAnnotationEqualityProof.pairFields (next.relabel j) output (nextWork.relabel j) (nextResults.relabel j) newWork (results.relabel j) hp' hpair heq
 have hwEq := andLeft hfields
 have hafter := headTransport OriginalHereditaryAgendaPotential.agenda (after.relabel j) (nextWork.relabel j) newWork (Fin.cons (B.relabel j) Fin.elim0) hwEq hm'
 have hdrop := OriginalHereditaryAgendaPotentialVisitProof.actualVisitReplacement body beta Theta
   (parent.relabel j) (frame.relabel j) returnFrame payload (jobs.relabel j) tagged (rest.relabel j) (work.relabel j)
   returnRest newWork (B.relabel j) (weight.relabel j) (before.relabel j) (after.relabel j)
   hf' hreturn hc' hreturnRest he' htagged happ hweight' hbound' hb' hafter
 have hagenda := visitPres body beta Theta H M W (c.relabel j) (B.relabel j) (work.relabel j) (frame.relabel j) (rest.relabel j)
   (parent.relabel j) (jobs.relabel j) tagged counts payload returnFrame returnRest newWork
   ha' hc' hf' he' htagged hpay hreturn hreturnRest happ
 obtain ⟨hwEq⟩ := hwEq
 have hinv := OriginalHereditaryInternalAgendaTransportProof.agendaTransport H M W (c.relabel j) (B.relabel j) newWork (nextWork.relabel j)
  (by simpa only [equalEqn] using (Nonempty.intro (symm hwEq))) hagenda
 exact andIntro hinv hdrop
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryPotentialStepVisitProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryPotentialStepVisitProof
