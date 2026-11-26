module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.ProtectedPrefixWorkingTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.ProtectedAgendaProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAgendaVisitProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAdmissibleCombinedReturnProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.ProtectedPrefixSupport
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendFrameQueryProof (weakenProof)
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedSourceSyntaxProof (numeralRename)
open OriginalHereditaryInternalAgenda OriginalHereditaryInternalAgendaSyntaxProof
open ProtectedPrefixWorkingTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem weakenConsumer (R : Program 2) (H : Program 1) (M W : Program 2)
 (c B input suffix : OTerm alpha) (psi : Formula alpha) {Theta : List (Formula alpha)}
 (next : Consumer R H M W body Delta c B input suffix psi)
 (inc : ∀ f ∈ Delta, f ∈ Theta) : Consumer R H M W body Theta c B input suffix psi := by
 intro beta j Xi newPrefix nextWork nextResults output hinc hp ht ha hs
 exact next beta j Xi newPrefix nextWork nextResults output
   (fun f hf => hinc f (inc f hf)) hp ht ha hs
theorem renameConsumer (R : Program 2) (H : Program 1) (M W : Program 2)
 (c B input suffix : OTerm alpha) (psi : Formula alpha) {beta : Type}
 (j : alpha → beta) (Theta : List (Formula beta))
 (next : Consumer R H M W body Delta c B input suffix psi)
 (inc : ∀ f ∈ Delta, f.relabel j ∈ Theta) :
 Consumer R H M W body Theta (c.relabel j) (B.relabel j) (input.relabel j) (suffix.relabel j) (psi.relabel j) := by
 intro gamma k Xi newPrefix nextWork nextResults output hinc hp ht ha hs
 have h := next gamma (k ∘ j) Xi newPrefix nextWork nextResults output
   (by
     intro f hf
     simpa only [← InternalPositiveUnfoldingSupportProof.formulaRelabelComposition] using hinc _ (inc f hf)) hp
   (by simpa only [Term.relabel_relabel] using ht)
   (by simpa only [Term.relabel_relabel] using ha)
   (by simpa only [Term.relabel_relabel] using hs)
 simpa only [InternalPositiveUnfoldingSupportProof.formulaRelabelComposition] using h

theorem visit (R : Program 2) (H : Program 1) (M W : Program 2)
 (c B input work results frame rest parent jobs tail suffix : OTerm alpha) (psi : Formula alpha)
 (hs : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input work results)))
 (hw : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work frame rest)))
 (hf : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (numeral 0) parent)))
 (he : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.expansion jobs parent)))
 (ha : Nonempty (Derivation body Delta (Agenda H M W c B work)))
 (hrest : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append rest tail suffix)))
 (next : Consumer R H M W body Delta c B input suffix psi) : Nonempty (Derivation body Delta psi) := by
 apply OriginalHereditaryInternalVisitProof.visitCases R body alpha Delta input work results frame rest parent jobs psi hs hw hf he
 intro beta j Theta childCount deletionCount counts payload returnFrame tagged returnRest newWork output
   hinc _ _ _ hpay hreturn htag hreturnRest hscheduled hp ht
 have ha' := renameInto ha j Theta hinc
 have hw' := renameInto hw j Theta hinc
 have hf' := renameInto hf j Theta hinc
 have he' := renameInto he j Theta hinc
 have hrest' := renameInto hrest j Theta hinc
 simp only [agendaRename,graph1Rename,graph2Rename,numeralRename] at ha' hw' hf' he' hrest'
 have hnewAgenda := OriginalHereditaryInternalAgendaVisitProof.actualVisitPreservation body beta Theta H M W
   (c.relabel j) (B.relabel j) (work.relabel j) (frame.relabel j) (rest.relabel j) (parent.relabel j)
   (jobs.relabel j) tagged counts payload returnFrame returnRest newWork ha' hw' hf' he' htag hpay hreturn hreturnRest hscheduled
 have consume := renameConsumer R H M W c B input suffix psi j Theta next hinc
 apply ProtectedAgendaProof.scheduledSuffixCases (tail.relabel j) (suffix.relabel j) (rest.relabel j)
   returnFrame tagged returnRest newWork (psi.relabel j) hrest' hreturnRest hscheduled
 intro gamma k Xi newPrefix hk hprotected
 have hp' := renameInto hp k Xi hk
 have ht' := renameInto ht k Xi hk
 have ha'' := renameInto hnewAgenda k Xi hk
 simp only [graph1Rename,graph2Rename,agendaRename] at hp' ht' ha''
 exact consume gamma k Xi newPrefix (newWork.relabel k) ((results.relabel j).relabel k) (output.relabel k)
   hk hp' ht' ha'' hprotected

theorem returnAtJob (R : Program 2) (H : Program 1) (M W : Program 2)
 (c B input work results frame rest payload parent counts tail suffix role typ typed rawJob raw parameter gamma weight : OTerm alpha)
 (psi : Formula alpha)
 (hs : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input work results)))
 (hw : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work frame rest)))
 (hf : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (numeral 1) payload)))
 (hpay : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload parent counts)))
 (hj : Nonempty (Derivation body Delta (jobFields H M W c B parent role typ typed rawJob raw parameter gamma weight)))
 (ha : Nonempty (Derivation body Delta (Agenda H M W c B work)))
 (hrest : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append rest tail suffix)))
 (next : Consumer R H M W body Delta c B input suffix psi) : Nonempty (Derivation body Delta psi) := by
 have htail := OriginalHereditaryInternalAgendaStructuralProof.tail H M W c B work frame rest ha hw
 apply OriginalInternalAdmissibleCombinedReturnProof.actualReturn R body H M W alpha Delta
   input work results frame rest payload parent counts role typed typ rawJob raw parameter c gamma psi
   hs hw hf hpay (andLeft hj) (andLeft (andRight hj)) (andLeft (andRight (andRight hj)))
   (andLeft (andRight (andRight (andRight hj)))) (andLeft (andRight (andRight (andRight (andRight hj)))))
 intro beta j Theta output newResults hinc hp ht
 have ha' := renameInto htail j Theta hinc
 rw [agendaRename] at ha'
 have hrest' := renameInto hrest j Theta hinc
 rw [graph2Rename] at hrest'
 exact next beta j Theta (tail.relabel j) (rest.relabel j) newResults output hinc hp ht ha' hrest'

theorem returnCase (R : Program 2) (H : Program 1) (M W : Program 2)
 (c B input work results frame rest payload parent counts tail suffix : OTerm alpha) (psi : Formula alpha)
 (hs : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input work results)))
 (hw : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work frame rest)))
 (hf : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (numeral 1) payload)))
 (hpay : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload parent counts)))
 (hj : Nonempty (Derivation body Delta (Job H M W c B parent)))
 (ha : Nonempty (Derivation body Delta (Agenda H M W c B work)))
 (hrest : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append rest tail suffix)))
 (next : Consumer R H M W body Delta c B input suffix psi) : Nonempty (Derivation body Delta psi) := by
 apply OriginalHereditaryInternalAgendaBindingProof.jobCases H M W c B parent psi hj
 intro beta j Theta role typ typed rawJob raw parameter gamma weight hinc hfields
 have hs' := renameInto hs j Theta hinc
 have hw' := renameInto hw j Theta hinc
 have hf' := renameInto hf j Theta hinc
 have hpay' := renameInto hpay j Theta hinc
 have ha' := renameInto ha j Theta hinc
 have hrest' := renameInto hrest j Theta hinc
 simp only [graph1Rename,graph2Rename,numeralRename,agendaRename] at hs' hw' hf' hpay' ha' hrest'
 exact returnAtJob R H M W (c.relabel j) (B.relabel j) (input.relabel j) (work.relabel j) (results.relabel j)
   (frame.relabel j) (rest.relabel j) (payload.relabel j) (parent.relabel j) (counts.relabel j) (tail.relabel j) (suffix.relabel j)
   role typ typed rawJob raw parameter gamma weight (psi.relabel j) hs' hw' hf' hpay' hfields ha' hrest'
   (renameConsumer R H M W c B input suffix psi j Theta next hinc)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.ProtectedPrefixSupport
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.ProtectedPrefixSupport
