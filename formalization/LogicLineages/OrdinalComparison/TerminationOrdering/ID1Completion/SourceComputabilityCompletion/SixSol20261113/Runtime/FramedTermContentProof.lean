module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.FramedTermQueries
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.FramedValueAgreementProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.FramedTermContentProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem fromFields (R : Program 2) (H : Program 1) (M W : Program 2)
 (c B job typed typ rawJob raw parameter count value : OTerm alpha)
 (hadm : Nonempty (Derivation body Delta (OriginalHereditaryInternalAgenda.Job H M W c B job)))
 (hj : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job (numeral 0) typed)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawJob)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
 (hf : Nonempty (Derivation body Delta (SixSol20261112.Runtime.FramedCompletionDefinitions.Framed R job count value))) :
 Nonempty (Derivation body Delta (graph1 (SixSol20261113.Context.ChildContentDefinitions.observationFromJob (OriginalHereditaryEvaluatorDefinitions.evaluator R)) value job)) := by
 apply programCases InternalPairing.pairing (Fin.cons typ (Fin.cons raw Fin.elim0)) _
 intro beta j Theta packed hinc hp
 simp only [consTermRename,emptyRename] at hp
 have hadm' := renameInto hadm j Theta hinc
 have hj' := renameInto hj j Theta hinc
 have ht' := renameInto ht j Theta hinc
 have hr' := renameInto hr j Theta hinc
 have hf' := renameInto hf j Theta hinc
 simp only [OriginalHereditaryInternalAgendaSyntaxProof.jobRename,JobFrameSyntax.frameRename,graph2Rename,numeralRename] at hadm' hj' ht' hr' hf'
 have hgjob := FramedTermCodecProof.jobGraph (job.relabel j) (typed.relabel j) (typ.relabel j) (rawJob.relabel j) (raw.relabel j) (parameter.relabel j) packed hj' ht' hr' hp
 have heval := FramedTermQueries.evaluatorValue R H M W (c.relabel j) (B.relabel j) (job.relabel j) packed (parameter.relabel j) (count.relabel j) (value.relabel j) hadm' hgjob hf'
 rw [graph1Rename]
 exact FramedTermCodecProof.observedValue (OriginalHereditaryEvaluatorDefinitions.evaluator R) (job.relabel j) (typed.relabel j) (typ.relabel j) (rawJob.relabel j) (raw.relabel j) (parameter.relabel j) packed (value.relabel j) hj' ht' hr' hp heval

theorem actualTermFramedContent : FramedValueTargets.ActualTermFramedContent := by
 intro R H M W body alpha Delta c B job count value hadm hrole hf
 apply OriginalHereditaryInternalAgendaBindingProof.jobCases H M W c B job _ hadm
 intro beta j Theta role typ typed rawJob raw parameter gamma weight hinc fields
 have hadm' := renameInto hadm j Theta hinc
 have hrole' := renameInto hrole j Theta hinc
 have hf' := renameInto hf j Theta hinc
 simp only [OriginalHereditaryInternalAgendaSyntaxProof.jobRename,graph1Rename,numeralRename,JobFrameSyntax.frameRename] at hadm' hrole' hf'
 have hright := pairRight (job.relabel j) role typed (andLeft fields)
 have hj := reconstructPair (job.relabel j) (numeral 0) typed hrole' hright
 rw [graph1Rename]
 exact fromFields R H M W (c.relabel j) (B.relabel j) (job.relabel j) typed typ rawJob raw parameter (count.relabel j) (value.relabel j) hadm' hj (andLeft (andRight fields)) (andLeft (andRight (andRight fields))) hf'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.FramedTermContentProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.FramedTermContentProof
