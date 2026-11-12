module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryPotentialCompletionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAdmissibleCombinedReturnProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAgendaStructuralProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAgendaTransportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaPotentialReturnProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAnnotationEqualityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryPotentialStepFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAgendaBindingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryPotentialStepFrameProof
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
theorem atFrameFields (visitPres : OriginalHereditaryInternalAgendaTargets.VisitPreservation)
 (R : Program 2) (H : Program 1) (M W : Program 2)
 (c B input work results before next nextWork nextResults after frame rest payload parent counts : OTerm alpha)
 (hs : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input work results)))
 (ha : Nonempty (Derivation body Delta (Agenda H M W c B work)))
 (hb : Nonempty (Derivation body Delta (graph2 OriginalHereditaryAgendaPotential.agenda before work B)))
 (hn : Nonempty (Derivation body Delta (graph1 (OriginalHereditaryCombinedStep.step R) next input)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing next nextWork nextResults)))
 (hm : Nonempty (Derivation body Delta (graph2 OriginalHereditaryAgendaPotential.agenda after nextWork B)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work frame rest)))
 (hf : Nonempty (Derivation body Delta (frameFields H M W c B frame parent payload counts))) :
 Nonempty (Derivation body Delta (Agenda H M W c B nextWork ⊓ ltF after before)) := by
 apply OriginalHereditaryInternalAgendaBindingProof.jobCases H M W c B parent _ (andRight hf)
 intro beta j Theta role typ typed rawJob raw parameter gamma weight hinc hjob
 simp only [conjunctionRename,agendaRename,orderRename]
 have hs' := renameInto hs j Theta hinc
 have ha' := renameInto ha j Theta hinc
 have hb' := renameInto hb j Theta hinc
 have hn' := renameInto hn j Theta hinc
 have hp' := renameInto hp j Theta hinc
 have hm' := renameInto hm j Theta hinc
 have hc' := renameInto hc j Theta hinc
 have hf' := renameInto hf j Theta hinc
 simp only [graph1Rename,graph2Rename,agendaRename,frameFieldsRename] at hs' ha' hb' hn' hp' hm' hc' hf'
 exact OriginalHereditaryPotentialStepFieldsProof.atJobFields visitPres R H M W
  (c.relabel j) (B.relabel j) (input.relabel j) (work.relabel j) (results.relabel j) (before.relabel j) (next.relabel j) (nextWork.relabel j) (nextResults.relabel j) (after.relabel j) (frame.relabel j) (rest.relabel j) (payload.relabel j) (parent.relabel j) (counts.relabel j) role typ typed rawJob raw parameter gamma weight
  hs' ha' hb' hn' hp' hm' hc' (andLeft hf') hjob
theorem atFrame (visitPres : OriginalHereditaryInternalAgendaTargets.VisitPreservation)
 (R : Program 2) (H : Program 1) (M W : Program 2)
 (c B input work results before next nextWork nextResults after frame rest : OTerm alpha)
 (hs : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input work results)))
 (ha : Nonempty (Derivation body Delta (Agenda H M W c B work)))
 (hb : Nonempty (Derivation body Delta (graph2 OriginalHereditaryAgendaPotential.agenda before work B)))
 (hn : Nonempty (Derivation body Delta (graph1 (OriginalHereditaryCombinedStep.step R) next input)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing next nextWork nextResults)))
 (hm : Nonempty (Derivation body Delta (graph2 OriginalHereditaryAgendaPotential.agenda after nextWork B)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work frame rest)))
 (hf : Nonempty (Derivation body Delta (Frame H M W c B frame))) :
 Nonempty (Derivation body Delta (Agenda H M W c B nextWork ⊓ ltF after before)) := by
 apply OriginalHereditaryInternalAgendaBindingProof.frameCases H M W c B frame _ hf
 intro beta j Theta parent payload counts hinc hfields
 simp only [conjunctionRename,agendaRename,orderRename]
 have hs' := renameInto hs j Theta hinc
 have ha' := renameInto ha j Theta hinc
 have hb' := renameInto hb j Theta hinc
 have hn' := renameInto hn j Theta hinc
 have hp' := renameInto hp j Theta hinc
 have hm' := renameInto hm j Theta hinc
 have hc' := renameInto hc j Theta hinc
 simp only [graph1Rename,graph2Rename,agendaRename] at hs' ha' hb' hn' hp' hm' hc'
 exact atFrameFields visitPres R H M W
  (c.relabel j) (B.relabel j) (input.relabel j) (work.relabel j) (results.relabel j) (before.relabel j) (next.relabel j) (nextWork.relabel j) (nextResults.relabel j) (after.relabel j) (frame.relabel j) (rest.relabel j) payload parent counts hs' ha' hb' hn' hp' hm' hc' hfields
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryPotentialStepFrameProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryPotentialStepFrameProof
