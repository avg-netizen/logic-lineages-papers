module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAgendaStructuralProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAppendLookupStatementChecks
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAgendaAppendProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof
open InternalApplicationValidityStackAppendFrameQueryProof (weakenProof)
open OriginalHereditaryInternalAgenda OriginalHereditaryInternalAgendaSyntaxProof
open OriginalHereditaryInternalAgendaBindingProof
open OriginalContextInsertion
open OriginalContextInsertionSyntaxProof (lengthRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem append (H : Program 1) (M W : Program 2) (c B front suffix joined : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (Agenda H M W c B front)))
 (hs : Nonempty (Derivation body Delta (Agenda H M W c B suffix)))
 (ha : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append joined front suffix))) :
 Nonempty (Derivation body Delta (Agenda H M W c B joined)) := by
 apply InternalAcceptanceSupportProof.programCases length (Fin.cons front Fin.elim0) _
 intro beta j Theta frontCount hinc hl
 simp only [consTermRename,emptyRename] at hl
 have hf' := renameInto hf j Theta hinc
 have hs' := renameInto hs j Theta hinc
 have ha' := renameInto ha j Theta hinc
 simp only [agendaRename,graph2Rename] at hf' hs' ha'
 rw [agendaRename]
 apply agendaIntro H M W (c.relabel j) (B.relabel j) (joined.relabel j)
 intro gamma k Xi count index frame hk hfields
 have hf'' := renameInto hf' k Xi hk
 have hs'' := renameInto hs' k Xi hk
 have ha'' := renameInto ha' k Xi hk
 have hl' := renameInto hl k Xi hk
 simp only [agendaRename,graph2Rename,graph1Rename] at hf'' hs'' ha'' hl'
 have split := OriginalInternalAppendLookupStatementChecks.actualSplit body gamma Xi
  (frontCount.relabel k) ((front.relabel j).relabel k) ((suffix.relabel j).relabel k) ((joined.relabel j).relabel k)
  count index frame hl' ha'' (andLeft hfields) (andLeft (andRight hfields)) (andRight (andRight hfields))
 apply OriginalRawSyntaxTransportInternalConstructorArityCasesProof.orCases split
 · intro Omega inc hfront
   exact agendaApply H M W ((c.relabel j).relabel k) ((B.relabel j).relabel k)
    ((front.relabel j).relabel k) (frontCount.relabel k) index frame (weakenProof hf'' inc)
    (andIntro (weakenProof hl' inc) hfront)
 · intro Omega inc htail
   apply OriginalInternalAppendLookupBindingProof.tailCases (frontCount.relabel k) ((suffix.relabel j).relabel k) index frame _ htail
   intro epsilon l Psi suffixIndex suffixCount hli htailFields
   have hss := renameInto (weakenProof hs'' inc) l Psi hli
   rw [agendaRename] at hss
   rw [frameRename]
   exact agendaApply H M W (((c.relabel j).relabel k).relabel l) (((B.relabel j).relabel k).relabel l)
    (((suffix.relabel j).relabel k).relabel l) suffixCount suffixIndex (frame.relabel l) hss
    (andRight htailFields)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAgendaAppendProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAgendaAppendProof
