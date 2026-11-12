module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAgendaTransportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalFinitePrefixProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetSumBoundCellsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAgendaStructuralProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof (symm)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalApplicationValidityStackAppendFrameQueryProof (weakenProof)
open InternalRecursionGraphStepSyntaxProof
open OriginalContextInsertion OriginalContextInsertionLengthProof
open OriginalContextInsertionSyntaxProof (lengthRename)
open OriginalHereditaryInternalAgenda OriginalHereditaryInternalAgendaSyntaxProof
open OriginalHereditaryInternalAgendaBindingProof OriginalHereditaryInternalAgendaTransportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem visitFrame (H : Program 1) (M W : Program 2) (c B frame parent : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (numeral 0) parent)))
 (hp : Nonempty (Derivation body Delta (Job H M W c B parent))) :
 Nonempty (Derivation body Delta (Frame H M W c B frame)) :=
 frameIntro H M W c B frame parent z z (andIntro (Nonempty.intro (InternalQuotientComparisonProof.orLeft (Classical.choice hf))) hp)
theorem returnFrame (H : Program 1) (M W : Program 2) (c B frame parent payload counts : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (numeral 1) payload)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload parent counts)))
 (hp : Nonempty (Derivation body Delta (Job H M W c B parent))) :
 Nonempty (Derivation body Delta (Frame H M W c B frame)) :=
 frameIntro H M W c B frame parent payload counts (andIntro (Nonempty.intro (InternalQuotientComparisonProof.orRight (Classical.choice (andIntro hf hc)))) hp)

theorem nil (H : Program 1) (M W : Program 2) (c B : OTerm alpha) :
 Nonempty (Derivation body Delta (Agenda H M W c B z)) := by
 apply agendaIntro H M W c B z
 intro beta j Theta count index frame hinc hf
 simp only [zRelabel] at hf
 obtain ⟨hl⟩ := lengthNilRecover count (andLeft hf)
 obtain ⟨hb⟩ := andLeft (andRight hf)
 obtain ⟨hn⟩ := InternalApplicationValidityStackAppendTransitionProof.notLessZero (body:=body) (Gamma:=Theta) index
 exact ⟨Derivation.explosion (Derivation.implicationElimination hn (InternalSquareRootArithmeticSupportProof.orderRight index hl hb))⟩

theorem cons (H : Program 1) (M W : Program 2) (c B work head rest : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work head rest)))
 (hh : Nonempty (Derivation body Delta (Frame H M W c B head)))
 (hr : Nonempty (Derivation body Delta (Agenda H M W c B rest))) :
 Nonempty (Derivation body Delta (Agenda H M W c B work)) := by
 apply agendaIntro H M W c B work
 intro beta j Theta count index frame hinc hf
 have hc' := renameInto hc j Theta hinc
 have hh' := renameInto hh j Theta hinc
 have hr' := renameInto hr j Theta hinc
 simp only [graph2Rename] at hc'
 rw [frameRename] at hh'
 rw [agendaRename] at hr'
 apply OriginalHereditaryInternalFinitePrefixProof.boundedCons body beta Theta
  (work.relabel j) (head.relabel j) (rest.relabel j) count index frame _ hc'
  (andLeft hf) (andLeft (andRight hf)) (andRight (andRight hf))
 · intro Xi inc he
   obtain ⟨he⟩ := he
   exact frameTransport H M W (c.relabel j) (B.relabel j) (head.relabel j) frame
    (by simpa only [equalEqn] using (Nonempty.intro (symm he))) (weakenProof hh' inc)
 · intro gamma k Xi pred tailCount hk hl hb hv
   have hr'' := renameInto hr' k Xi hk
   rw [agendaRename] at hr''
   rw [frameRename]
   exact agendaApply H M W ((c.relabel j).relabel k) ((B.relabel j).relabel k)
    ((rest.relabel j).relabel k) tailCount pred (frame.relabel k) hr'' (andIntro hl (andIntro hb hv))

theorem tail (H : Program 1) (M W : Program 2) (c B work head rest : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (Agenda H M W c B work)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work head rest))) :
 Nonempty (Derivation body Delta (Agenda H M W c B rest)) := by
 apply agendaIntro H M W c B rest
 intro beta j Theta count index frame hinc hf
 have ha' := renameInto ha j Theta hinc
 have hc' := renameInto hc j Theta hinc
 rw [agendaRename] at ha'
 rw [graph2Rename] at hc'
 have hl := lengthCons (work.relabel j) (head.relabel j) (rest.relabel j) count hc' (andLeft hf)
 have hb := InternalRecursionGraphExtensionSupportProof.successorOrder index count (andLeft (andRight hf))
 obtain ⟨hi⟩ := OriginalAllPositionContextDeleteDropProof.lookupConsIff (work.relabel j) (head.relabel j) (rest.relabel j) index frame hc'
 obtain ⟨hv⟩ := andRight (andRight hf)
 have hlk := Nonempty.intro (Derivation.implicationElimination (Derivation.conjunctionRight hi) hv)
 exact agendaApply H M W (c.relabel j) (B.relabel j) (work.relabel j) (suc count) (suc index) frame ha' (andIntro hl (andIntro hb hlk))

theorem head (H : Program 1) (M W : Program 2) (c B work head rest : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (Agenda H M W c B work)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work head rest))) :
 Nonempty (Derivation body Delta (Frame H M W c B head)) := by
 apply InternalAcceptanceSupportProof.programCases length (Fin.cons rest Fin.elim0) _
 intro beta j Theta count hinc hl
 simp only [consTermRename,emptyRename] at hl
 have ha' := renameInto ha j Theta hinc
 have hc' := renameInto hc j Theta hinc
 rw [agendaRename] at ha'
 rw [graph2Rename] at hc'
 rw [frameRename]
 exact agendaApply H M W (c.relabel j) (B.relabel j) (work.relabel j) (suc count) z (head.relabel j) ha'
  (andIntro (lengthCons (work.relabel j) (head.relabel j) (rest.relabel j) count hc' hl)
   (andIntro (OriginalHereditaryBudgetSumBoundCellsProof.zeroBound count)
    (OriginalAllPositionContextDeleteBaseProof.lookupZero (work.relabel j) (head.relabel j) (rest.relabel j) hc')))

theorem initial : OriginalHereditaryInternalAgendaTargets.Initial := by
 intro body alpha Delta H M W c B parent visit work hj hv hw
 exact cons H M W c B work visit z hw (visitFrame H M W c B visit parent hv hj) (nil H M W c B)
theorem returnPreservation : OriginalHereditaryInternalAgendaTargets.ReturnPreservation := by
 intro body alpha Delta H M W c B work frame rest ha hc
 exact tail H M W c B work frame rest ha hc
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAgendaStructuralProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAgendaStructuralProof
