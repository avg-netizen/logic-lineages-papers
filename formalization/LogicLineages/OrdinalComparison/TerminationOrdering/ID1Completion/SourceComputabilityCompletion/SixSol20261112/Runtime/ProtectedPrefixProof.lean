module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.ProtectedPrefixSupport
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.ProtectedPrefixProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open InternalApplicationValidityStackAppendFrameQueryProof (weakenProof)
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedSourceSyntaxProof (numeralRename)
open OriginalHereditaryInternalAgenda OriginalHereditaryInternalAgendaSyntaxProof
open ProtectedPrefixWorkingTargets ProtectedPrefixSupport
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem atFrameFields (R : Program 2) (H : Program 1) (M W : Program 2)
 (c B input work results frame rest parent payload counts tail suffix : OTerm alpha) (psi : Formula alpha)
 (hs : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input work results)))
 (hw : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work frame rest)))
 (hfields : Nonempty (Derivation body Delta (frameFields H M W c B frame parent payload counts)))
 (ha : Nonempty (Derivation body Delta (Agenda H M W c B work)))
 (hrest : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append rest tail suffix)))
 (next : Consumer R H M W body Delta c B input suffix psi) : Nonempty (Derivation body Delta psi) := by
 apply OriginalRawSyntaxTransportInternalConstructorArityCasesProof.orCases (andLeft hfields)
 · intro Omega inc hvisit
   apply programCases OriginalHereditaryAnnotatedExpansion.expansion (Fin.cons parent Fin.elim0) _
   intro beta j Theta jobs hinc he
   simp only [consTermRename,emptyRename] at he
   have hs' := renameInto (weakenProof hs inc) j Theta hinc
   have hw' := renameInto (weakenProof hw inc) j Theta hinc
   have hv' := renameInto hvisit j Theta hinc
   have ha' := renameInto (weakenProof ha inc) j Theta hinc
   have hr' := renameInto (weakenProof hrest inc) j Theta hinc
   simp only [graph1Rename,graph2Rename,numeralRename,agendaRename] at hs' hw' hv' ha' hr'
   exact ProtectedPrefixSupport.visit R H M W (c.relabel j) (B.relabel j) (input.relabel j) (work.relabel j)
     (results.relabel j) (frame.relabel j) (rest.relabel j) (parent.relabel j) jobs (tail.relabel j) (suffix.relabel j)
     (psi.relabel j) hs' hw' hv' he ha' hr'
     (renameConsumer R H M W c B input suffix psi j Theta
       (weakenConsumer R H M W c B input suffix psi next inc) hinc)
 · intro Omega inc hreturn
   exact ProtectedPrefixSupport.returnCase R H M W c B input work results frame rest payload parent counts tail suffix psi
     (weakenProof hs inc) (weakenProof hw inc) (andLeft hreturn) (andRight hreturn)
     (weakenProof (andRight hfields) inc) (weakenProof ha inc) (weakenProof hrest inc)
     (weakenConsumer R H M W c B input suffix psi next inc)

theorem atFrame (R : Program 2) (H : Program 1) (M W : Program 2)
 (c B input work results frame rest tail suffix : OTerm alpha) (psi : Formula alpha)
 (hs : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input work results)))
 (hw : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work frame rest)))
 (hf : Nonempty (Derivation body Delta (Frame H M W c B frame)))
 (ha : Nonempty (Derivation body Delta (Agenda H M W c B work)))
 (hrest : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append rest tail suffix)))
 (next : Consumer R H M W body Delta c B input suffix psi) : Nonempty (Derivation body Delta psi) := by
 apply OriginalHereditaryInternalAgendaBindingProof.frameCases H M W c B frame psi hf
 intro beta j Theta parent payload counts hinc hfields
 have hs' := renameInto hs j Theta hinc
 have hw' := renameInto hw j Theta hinc
 have ha' := renameInto ha j Theta hinc
 have hr' := renameInto hrest j Theta hinc
 simp only [graph1Rename,graph2Rename,numeralRename,agendaRename] at hs' hw' ha' hr'
 exact atFrameFields R H M W (c.relabel j) (B.relabel j) (input.relabel j) (work.relabel j)
   (results.relabel j) (frame.relabel j) (rest.relabel j) parent payload counts (tail.relabel j) (suffix.relabel j)
   (psi.relabel j) hs' hw' hfields ha' hr'
   (renameConsumer R H M W c B input suffix psi j Theta next hinc)

theorem actualStepCases : ProtectedPrefixWorkingTargets.ActualStepCases := by
 intro R H M W body alpha Delta c B input work results front head tail suffix psi hs happ hc ha next
 apply programCases InternalApplicationValidityStackAppend.append (Fin.cons tail (Fin.cons suffix Fin.elim0)) _
 intro beta j Theta rest hinc hrest
 simp only [consTermRename,emptyRename] at hrest
 have hs' := renameInto hs j Theta hinc
 have happ' := renameInto happ j Theta hinc
 have hc' := renameInto hc j Theta hinc
 have ha' := renameInto ha j Theta hinc
 simp only [graph1Rename,graph2Rename,agendaRename] at hs' happ' hc' ha'
 have hw := InternalApplicationValidityStackAppendListProof.consForward
   (front.relabel j) (head.relabel j) (tail.relabel j) (suffix.relabel j) rest (work.relabel j) hc' hrest happ'
 have hf := OriginalHereditaryInternalAgendaStructuralProof.head H M W
   (c.relabel j) (B.relabel j) (work.relabel j) (head.relabel j) rest ha' hw
 exact atFrame R H M W (c.relabel j) (B.relabel j) (input.relabel j) (work.relabel j)
   (results.relabel j) (head.relabel j) rest (tail.relabel j) (suffix.relabel j) (psi.relabel j)
   hs' hw hf ha' hrest (renameConsumer R H M W c B input suffix psi j Theta next hinc)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.ProtectedPrefixProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.ProtectedPrefixProof
