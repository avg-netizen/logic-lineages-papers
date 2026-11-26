module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentArgumentMetadataQueries
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentArgumentNormalizationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.FramedTermContentProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAgendaBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentLocalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalHereditaryInternalAgendaSyntaxProof (jobRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Runtime FramedContentDefinitions
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem fromFields (R : Program 2) (H : Program 1) (M W : Program 2)
 (c B job role typed typ rawJob raw parameter gamma jobs size count value : OTerm alpha)
 (hJob : Nonempty (Derivation body Delta (OriginalHereditaryInternalAgenda.Job H M W c B job)))
 (hj : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job role typed)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawJob)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (ha : Nonempty (Derivation body Delta (OriginalInternalJobAdmissible.Admissible H M W role typ raw gamma c)))
 (he : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.expansion jobs job)))
 (hl : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph size jobs)))
 (hall : Nonempty (Derivation body Delta (VisitListCompletionDefinitions.AllComplete R size jobs)))
 (hcontent : Nonempty (Derivation body Delta (ContentVisitsDefinitions.AllContent R size jobs)))
 (hf : Nonempty (Derivation body Delta (SixSol20261112.Runtime.FramedCompletionDefinitions.Framed R job count value))) :
 Nonempty (Derivation body Delta (Content R job value)) := by
 apply OriginalTypedDecoderInternalBranchProof.orCases ha
 · let A := equal role (numeral 0) ⊓ OriginalUniverseDecoderInternalAcceptance.TermAccepted H M W typ raw gamma c
   have hA : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
   have hrole := andLeft hA
   rw [equalEqn] at hrole
   have hleft := outputTransport InternalUnpair.left role (numeral 0) (Fin.cons job Fin.elim0)
     hrole (pairLeft job role typed (withHyp hj A))
   exact FramedTermContentProof.actualTermFramedContent R H M W body alpha (A :: Delta)
     c B job count value (withHyp hJob A) hleft (withHyp hf A)
 · let A := equal role (numeral 1) ⊓ (equal typ (numeral 0) ⊓ OriginalInternalJobAdmissible.ArgumentsWitness H M W raw gamma c)
   have hA : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
   have hs := FramedContentArgumentNormalizationProof.actualFields H M W job role typed typ rawJob raw gamma c
     (withHyp hj A) (withHyp ht A) (withHyp ha A) (andLeft hA) (andLeft (andRight hA))
   exact FramedContentArgumentMetadataQueries.fromFields R H M W job typed rawJob raw parameter c gamma jobs size count value
     (andLeft hs) (andLeft (andRight hs)) (withHyp hr A) (withHyp hp A) (andRight (andRight hs))
     (withHyp he A) (withHyp hl A) (withHyp hall A) (withHyp hcontent A) (withHyp hf A)

theorem actualLocalContent (R : Program 2) (H : Program 1) (M W : Program 2)
 (c B job jobs size count value : OTerm alpha)
 (hj : Nonempty (Derivation body Delta (OriginalHereditaryInternalAgenda.Job H M W c B job)))
 (he : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.expansion jobs job)))
 (hl : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph size jobs)))
 (hall : Nonempty (Derivation body Delta (VisitListCompletionDefinitions.AllComplete R size jobs)))
 (hcontent : Nonempty (Derivation body Delta (ContentVisitsDefinitions.AllContent R size jobs)))
 (hf : Nonempty (Derivation body Delta (SixSol20261112.Runtime.FramedCompletionDefinitions.Framed R job count value))) :
 Nonempty (Derivation body Delta (Content R job value)) := by
 apply OriginalHereditaryInternalAgendaBindingProof.jobCases H M W c B job _ hj
 intro beta j Theta role typ typed rawJob raw parameter gamma weight hinc hfields
 have hj' := renameInto hj j Theta hinc
 have he' := renameInto he j Theta hinc
 have hl' := renameInto hl j Theta hinc
 have hall' := renameInto hall j Theta hinc
 have hcontent' := renameInto hcontent j Theta hinc
 have hf' := renameInto hf j Theta hinc
 simp only [jobRename,graph1Rename,OriginalContextInsertionSyntaxProof.lengthRename,
   VisitListCompletionSyntax.allRename,ContentVisitsSyntax.allRename,JobFrameSyntax.frameRename]
   at hj' he' hl' hall' hcontent' hf'
 simp only [Content,graph1Rename]
 exact fromFields R H M W (c.relabel j) (B.relabel j) (job.relabel j) role typed typ rawJob raw parameter gamma
   (jobs.relabel j) (size.relabel j) (count.relabel j) (value.relabel j) hj'
   (andLeft hfields) (andLeft (andRight hfields)) (andLeft (andRight (andRight hfields)))
   (andLeft (andRight (andRight (andRight hfields))))
   (andLeft (andRight (andRight (andRight (andRight hfields))))) he' hl' hall' hcontent' hf'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentLocalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentLocalProof
