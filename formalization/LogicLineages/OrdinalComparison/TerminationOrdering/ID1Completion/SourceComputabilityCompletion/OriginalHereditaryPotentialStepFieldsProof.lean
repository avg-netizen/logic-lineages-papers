module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryPotentialCompletionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAdmissibleCombinedReturnProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAgendaStructuralProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAgendaTransportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaPotentialReturnProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAnnotationEqualityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryPotentialStepReturnProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryPotentialStepVisitProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryPotentialStepFieldsProof
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
open InternalAcceptanceSupportProof (programCases)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open OriginalTypedDecoderInternalBranchProof (orCases)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
theorem atJobFields (visitPres : OriginalHereditaryInternalAgendaTargets.VisitPreservation)
 (R : Program 2) (H : Program 1) (M W : Program 2)
 (c B input work results before next nextWork nextResults after frame rest payload parent counts
 role typ typed rawJob raw parameter gamma weight : OTerm alpha)
 (hs : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input work results)))
 (ha : Nonempty (Derivation body Delta (Agenda H M W c B work)))
 (hb : Nonempty (Derivation body Delta (graph2 OriginalHereditaryAgendaPotential.agenda before work B)))
 (hn : Nonempty (Derivation body Delta (graph1 (OriginalHereditaryCombinedStep.step R) next input)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing next nextWork nextResults)))
 (hm : Nonempty (Derivation body Delta (graph2 OriginalHereditaryAgendaPotential.agenda after nextWork B)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work frame rest)))
 (hf : Nonempty (Derivation body Delta
  (graph2 InternalPairing.pairing frame (numeral 0) parent ⊔
   (graph2 InternalPairing.pairing frame (numeral 1) payload ⊓ graph2 InternalPairing.pairing payload parent counts))))
 (hj : Nonempty (Derivation body Delta (jobFields H M W c B parent role typ typed rawJob raw parameter gamma weight))) :
 Nonempty (Derivation body Delta (Agenda H M W c B nextWork ⊓ ltF after before)) := by
 let A := graph2 InternalPairing.pairing frame (numeral 0) parent
 let C := graph2 InternalPairing.pairing frame (numeral 1) payload ⊓ graph2 InternalPairing.pairing payload parent counts
 apply orCases hf
 · have hvisit : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
   have hsA := withHyp hs A
   have haA := withHyp ha A
   have hbA := withHyp hb A
   have hnA := withHyp hn A
   have hpA := withHyp hp A
   have hmA := withHyp hm A
   have hcA := withHyp hc A
   have hjA := withHyp hj A
   apply programCases OriginalHereditaryAnnotatedExpansion.expansion (Fin.cons parent Fin.elim0) _
   intro beta j Theta jobs hinc he
   simp only [conjunctionRename,agendaRename,orderRename]
   simp only [consTermRename,emptyRename] at he
   have hs' := renameInto hsA j Theta hinc
   have ha' := renameInto haA j Theta hinc
   have hb' := renameInto hbA j Theta hinc
   have hn' := renameInto hnA j Theta hinc
   have hp' := renameInto hpA j Theta hinc
   have hm' := renameInto hmA j Theta hinc
   have hc' := renameInto hcA j Theta hinc
   have hj' := renameInto hjA j Theta hinc
   have hvisit' := renameInto hvisit j Theta hinc
   simp only [A,graph1Rename,graph2Rename,agendaRename,jobFieldsRename,numeralRename] at hs' ha' hb' hn' hp' hm' hc' hj' hvisit'
   exact OriginalHereditaryPotentialStepVisitProof.visitProgress visitPres R H M W
    (c.relabel j) (B.relabel j) (input.relabel j) (work.relabel j) (results.relabel j) (before.relabel j) (next.relabel j) (nextWork.relabel j) (nextResults.relabel j) (after.relabel j) (frame.relabel j) (rest.relabel j) (parent.relabel j) jobs (weight.relabel j)
    hs' ha' hb' hn' hp' hm' hc' hvisit' he
    (andLeft (andRight (andRight (andRight (andRight (andRight hj'))))))
    (andRight (andRight (andRight (andRight (andRight (andRight hj'))))))
 · have hreturn : Nonempty (Derivation body (C :: Delta) C) := ⟨Derivation.hypothesis List.mem_cons_self⟩
   exact OriginalHereditaryPotentialStepReturnProof.returnProgress R H M W
     c B input work results before next nextWork nextResults after frame rest payload parent counts
     role typ typed rawJob raw parameter gamma weight
     (withHyp hs C) (withHyp ha C) (withHyp hb C) (withHyp hn C) (withHyp hp C) (withHyp hm C) (withHyp hc C)
     (andLeft hreturn) (andRight hreturn) (withHyp hj C)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryPotentialStepFieldsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryPotentialStepFieldsProof
